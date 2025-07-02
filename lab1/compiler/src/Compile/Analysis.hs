module Compile.Analysis where

import Data.List hiding (union)
import Data.Set (Set, union, notMember)
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import qualified Data.Vector.Mutable as MVec
import Control.Monad.ST
import Control.Monad.Reader
import Control.Monad.State
import Data.STRef
import Debug.Trace

import Compile.Types.Ops
import Compile.Types.Assembly (used, defined)
import Compile.Types.AbstractAssembly
import Compile.Types.X86_64


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
    info ins = (Vec.length ins - 1, Vec.map defined ins)
    local = used
    step (lastLine, defVars) vs = Vec.ifoldr' step' vs defVars
      where
        step' i def | i >= lastLine  = id  
                    | otherwise = Vec.modify $ \ liveVec -> do
                      thisLive <- MVec.read liveVec i
                      succLive <- MVec.read liveVec (i + 1)
                      let updateLive = thisLive `union`
                                       (Set.filter (`notMember` def) succLive)
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
