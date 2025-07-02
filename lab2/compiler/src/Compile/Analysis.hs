module Compile.Analysis where

import Data.List hiding (union)
import Data.Set (Set, union, notMember)
import qualified Data.Set as Set
import Data.Vector (Vector, (!))
import qualified Data.Vector as Vec
import qualified Data.Vector.Mutable as MVec
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.ST
import Control.Monad.Reader
import Control.Monad.State
import Data.STRef
import Debug.Trace

import Compile.Types.Ops
import Compile.Types.Assembly (used, defined, successors, LineID(..), reg)
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
    labelMap ins = Vec.ifoldr mkLabel Map.empty ins
    info ins = (Vec.length ins - 1, Vec.map defined ins,
                Vec.map successors ins, labelMap ins)
    local = used
    step (lastLine, defVars, succs, labels) vs = Vec.ifoldr' step' vs defVars
      where
        step' i def | i >= lastLine  = id  
                    | otherwise = Vec.modify $ \ liveVec -> do
                      thisLive <- MVec.read liveVec i
                      let succ = Set.toList $ succs ! i
                          readLabel NextLine = i + 1
                          readLabel (LineLabel s) = (Map.!) labels s
                      succsLive <- mapM (MVec.read liveVec . readLabel) succ
                      let updateLive = thisLive `union`
                                       (Set.filter (`notMember` def) $ Set.unions succsLive)
                      MVec.write liveVec i updateLive
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

translateAsm :: AAsm -> [Instr AVal]
translateAsm (AComment _) = []
translateAsm (ACtrl Ret a) = [MOVL a (ALoc $ AReg 0), RET]
translateAsm (AAsm [a] Add [b,c]) = [MOVL b (ALoc a), ADDL c (ALoc a)]
translateAsm (AAsm [a] Sub [b,c]) = [MOVL b (ALoc a), SUBL c (ALoc a)]
translateAsm (AAsm [a] Mul [b,c]) = [MOVL b (ALoc a), IMULL c (ALoc a)]
translateAsm (AAsm [a] Div [b,c]) = [MOVL b (ALoc $ AReg 0),
                                  CLTD,
                                  IDIVL c,
                                  MOVL (ALoc $ AReg 0) (ALoc a)]
translateAsm (AAsm [a] Neg [b]) = [MOVL b (ALoc a), NEGQ (ALoc a)]
translateAsm (AAsm [a] Mod [b,c]) = [MOVL b (ALoc $ AReg 0),
                                  CLTD,
                                  IDIVL c,
                                  MOVL (ALoc $ AReg 2) (ALoc a)] 
translateAsm (AAsm [a] Nop [b]) = [MOVL b (ALoc a)]
translateAsm (AAsm [a] Not [b]) = [MOVL b (ALoc a),
                                   NOTL (ALoc a)]
translateAsm (AAsm [a] Comp [b]) = [MOVL b (ALoc a),
                                    NOTL (ALoc a)]
translateAsm (AAsm [a] Lt [b,c]) = [MOVL (AImm false) (ALoc a),
                                   CMPL c b,
                                   CMOVL (AImm true) (ALoc a)
                                  ]
translateAsm (AAsm [a] LtE [b,c]) = [MOVL (AImm false) (ALoc a),
                                    CMPL c b,
                                    CMOVLE (AImm true) (ALoc a)
                                   ]
translateAsm (AAsm [a] Gt [b,c]) = [MOVL (AImm false) (ALoc a),
                                    CMPL c b,
                                    CMOVG (AImm true) (ALoc a)
                                   ]
translateAsm (AAsm [a] GtE [b,c]) = [MOVL (AImm false) (ALoc a),
                                    CMPL c b,
                                    CMOVGE (AImm true) (ALoc a)
                                   ]
translateAsm (AAsm [a] Eq [b,c]) = [MOVL (AImm false) (ALoc a),
                                    CMPL c b,
                                    CMOVE (AImm true) (ALoc a)
                                   ]
translateAsm (AAsm [a] NEq [b,c]) = [MOVL (AImm false) (ALoc a),
                                     CMPL c b,
                                     CMOVNE (AImm true) (ALoc a)
                                    ]
translateAsm (AAsm [a] AND [b,c]) = [MOVL b (ALoc a),
                                     ANDL c (ALoc a)
                                    ]
translateAsm (AAsm [a] XOR [b,c]) = [MOVL b (ALoc a),
                                     XORL c (ALoc a)
                                    ]
translateAsm (AAsm [a] OR [b,c]) = [MOVL b (ALoc a),
                                     ORL c (ALoc a)
                                    ]
translateAsm (AAsm [a] SL [b,c]) = [MOVL b (ALoc a),
                                    SALL c (ALoc a)
                                    ]                                   
translateAsm (AAsm [a] SR [b,c]) = [MOVL b (ALoc a),
                                    SARL c (ALoc a)
                                    ]
translateAsm (ALabel s) = [Label s]
translateAsm (AGoto s) = [JMP s]
translateAsm (AIfGoto e1 Eq e2 lbl) = [CMPL e2 e1,
                                       JE lbl]
translateAsm (AIfGoto e1 NEq e2 lbl) = [CMPL e2 e1,
                                        JNE lbl]									   
                                   
                                   


assemble :: [AAsm] -> [Instr AVal]
assemble = concat . map translateAsm



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
