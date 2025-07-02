{-# LANGUAGE PatternGuards #-}

module Compile.Analysis where

import Data.List hiding (union)
import Data.Set (Set, union, notMember)
import qualified Data.Set as Set
import Data.Vector (Vector, (!))
import qualified Data.Vector as Vec
import qualified Data.Vector.Mutable as MVec
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.ST
import Control.Monad.Reader
import Control.Monad.State
import Data.STRef
import Text.PrettyPrint.HughesPJ
import Debug.Trace

import Compile.Types.Ops
import Compile.Types.Assembly (used, defined, successors, LineID(..), reg,
                               Size(..))
import Compile.Types.AbstractAssembly
import Compile.Types.X86_64
import Compile.Translation (true, false)


propogate :: Eq a => (Vector ins -> info)    -- Context info
          -> (ins -> a)                     -- Local function to use
          -> (info -> Vector a -> Vector a)  -- Update the information 
          -> Vector ins                    
          -> Vector a                     
propogate info local step ins = calc init
  where
    context = info ins
    init = Vec.map local ins
    calc i = let next = step context i in
      if next /= i then calc next
      else i

liveness :: Vector (Instr AVal) -> Vector (Set AVal)
liveness = propogate info local step
  where
    mkLabel i (Label s) m = Map.insert s i m
    mkLabel _ _ m = m
    labelMap ins = Vec.ifoldr' mkLabel Map.empty ins
    info ins = (Vec.length ins - 1, Vec.map defined ins,
                Vec.map successors ins, labelMap ins)
    local = used
    step (lastLine, defVars, succs, labels) vs = Vec.ifoldr' step' vs defVars
      where
        step' i def = Vec.modify $ \ liveVec -> do
                      thisLive <- MVec.read liveVec i
                      let succ = Set.toList $ succs ! i
                          readLabel NextLine = i + 1
                          readLabel (LineLabel s) = (Map.!) labels s
                      succsLive <- mapM (MVec.read liveVec . readLabel) succ
                      let updateLive = thisLive `union`
                                       (Set.filter (`notMember` def) $ Set.unions succsLive)
                      MVec.write liveVec i updateLive

printVector :: Show a => Vector a -> String
printVector = Vec.foldr (\i rest -> (show i) ++ "\n" ++ rest) ""
                      
  {-
liveness (x : xs) = nub (live x) : restLive where
  restLive = liveness xs
  next = restLive >>= id
  live (MOVL s d) = delete d $ s : next
  live (ADDL s d) = delete d $ s : next
  live (SUBL s d) = delete d $ s : next
  live CLTD = next
  live (IMULL s d) = delete d $ s : next
  live (IDIVL a) = delete (ALoc $ AReg 0) $ delete (ALoc $ AReg 2) $ a : next
  live (NEGL d) = delete d $ next
-}

{-
maxSize :: AVal -> AVal -> Size
maxSize a b = max (size a) (size b)

translateAsm :: AAsm -> [Instr AVal]
translateAsm (AComment _) = []
translateAsm (ACtrl Ret a) = [MOVL a (ALoc (size a) $ AReg 0), RET]
translateAsm (AAsm [a] s Add [b@(ALoc _ b'),c])
  | b' == a = [ADDL c (ALoc s a)]
translateAsm (AAsm [a] s Add [b,c@(ALoc _ c')])
  | c' == a = [ADDL b (ALoc s a)]
translateAsm (AAsm [a] s Add [b,c]) = [MOVL b (ALoc s a),
                                       ADDL c (ALoc s a)]
translateAsm (AAsm [a] s Sub [b@(ALoc _ b'),c])
  | ALoc _ b' <- b, b' == a = [SUBL c (ALoc s a)]
translateAsm (AAsm [a] s Sub [b,c@(ALoc _ c')])
  | ALoc _ c' <- c, c' == a = [NEGQ (ALoc s a),
                               ADDL b (ALoc s a)]
translateAsm (AAsm [a] s Sub [b,c]) =  [MOVL b (ALoc s a),
                                        SUBL c (ALoc s a)]
translateAsm (AAsm [a] s Mul [b@(ALoc _ b'),c])
  | b' == a = [IMULL c (ALoc s a)]
translateAsm (AAsm [a] s Mul [b,c@(ALoc _ c')])
  | c' == a = [IMULL b (ALoc s a)]
translateAsm (AAsm [a] s Mul [b,c]) = [MOVL b (ALoc s a),
                                       IMULL c (ALoc s a)]
translateAsm (AAsm [a] _ Div [b,c]) = [MOVL b (ALoc L $ AReg 0),
                                       CLTD,
                                       IDIVL c,
                                       MOVL (ALoc L $ AReg 0) (ALoc L a)]
translateAsm (AAsm [a] _ Neg [b]) = [MOVL b (ALoc L a), NEGQ (ALoc L a)]
translateAsm (AAsm [a] _ Mod [b,c]) = [MOVL b (ALoc L $ AReg 0),
                                       CLTD,
                                       IDIVL c,
                                       MOVL (ALoc L $ AReg 2) (ALoc L a)] 
translateAsm (AAsm [a] s Nop [b]) = [MOVL b (ALoc s a)]
translateAsm (AAsm [a] _ Not [b]) = [MOVL b (ALoc L a),
                                   NOTL (ALoc L a),
                                   ANDL (AImm 1) (ALoc L a)]
translateAsm (AAsm [a] _ Comp [b]) = [MOVL b (ALoc L a),
                                    NOTL (ALoc L a)]
translateAsm (AAsm [a] _ Lt [b,c]) = [MOVL (AImm false) (ALoc L a),
                                   CMPL c b,
                                   CMOVL (AImm true) (ALoc L a)
                                  ]
translateAsm (AAsm [a] _ LtE [b,c]) = [MOVL (AImm false) (ALoc L a),
                                    CMPL c b,
                                    CMOVLE (AImm true) (ALoc L a)
                                   ]
translateAsm (AAsm [a] _ Gt [b,c]) = [MOVL (AImm false) (ALoc L a),
                                    CMPL c b,
                                    CMOVG (AImm true) (ALoc L a)
                                   ]
translateAsm (AAsm [a] _ GtE [b,c]) = [MOVL (AImm false) (ALoc L a),
                                    CMPL c b,
                                    CMOVGE (AImm true) (ALoc L a)
                                   ]
translateAsm (AAsm [a] _ Eq [b,c]) = [MOVL (AImm false) (ALoc L a),
                                    CMPL c b,
                                    CMOVE (AImm true) (ALoc L a)
                                   ]
translateAsm (AAsm [a] _ NEq [b,c]) = [MOVL (AImm false) (ALoc L a),
                                     CMPL c b,
                                     CMOVNE (AImm true) (ALoc L a)
                                    ]
translateAsm (AAsm [a] _ AND [b,c]) = [MOVL b (ALoc L a),
                                     ANDL c (ALoc L a)
                                    ]
translateAsm (AAsm [a] _ XOR [b,c]) = [MOVL b (ALoc L a),
                                     XORL c (ALoc L a)
                                    ]
translateAsm (AAsm [a] _ OR [b,c]) = [MOVL b (ALoc L a),
                                     ORL c (ALoc L a)
                                    ]
translateAsm (AAsm [a] _ SL [b,c]) = [MOVL b (ALoc L a),
                                      SALL c (ALoc L a)
                                     ]                                   
translateAsm (AAsm [a] _ SR [b,c]) = [MOVL b (ALoc L a),
                                      SARL c (ALoc L a)
                                     ]
translateAsm (ALabel s) = [Label s]
translateAsm (AGoto s) = [JMP s]
translateAsm (AIfGoto e1 Eq e2 lbl) = [CMPL e2 e1,
                                       JE lbl]
translateAsm (AIfGoto e1 NEq e2 lbl) = [CMPL e2 e1,
                                        JNE lbl]
translateAsm (AIfGoto e1 Lt e2 lbl) = [CMPL e2 e1,
                                        JL lbl]
translateAsm (AIfGoto e1 LtE e2 lbl) = [CMPL e2 e1,
                                        JLE lbl]
translateAsm (AIfGoto e1 Gt e2 lbl) = [CMPL e2 e1,
                                        JG lbl]
translateAsm (AIfGoto e1 GtE e2 lbl) = [CMPL e2 e1,
                                        JGE lbl]
translateAsm (ACall f v) = [CALL f v]
                                   
                                   


assemble :: Seq AAsm -> Seq (Instr AVal)
assemble ins = join (fmap translateAsm' ins) |> RET
  where
    translateAsm' = Seq.fromList . translateAsm
-}


{-
allocate :: Asm AVal -> Asm Expr
allocate = map (fmap assign)
  where
    assign (AImm i) = Const $ fromIntegral i
    assign (ALoc (ATemp i)) = Loc $ DerefOffset
                              (fromIntegral $ 4 * i)
                              $ Loc (Reg ESP)
    assign (ALoc (AReg i)) = Loc $ Reg $ toEnum i
-}
  

{-

live :: Code c => c -> Line c -> Set i
live c l = let
  instr = line c l
  init = used instr
  rest = live c (succ l)
  in
   init `union` Set.filter (`notMember` (defined instr)) rest
  
-}
