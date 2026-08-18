module LanguageDef.Test.PolyIndTypesTest

import Test.TestLibrary
import LanguageDef.PolyIndTypes
import LanguageDef.SlicePolyCat
import LanguageDef.SlicePolyUMorph
import LanguageDef.GenPolyFunc

%default total

-----------------------------------------
-----------------------------------------
---- Simple dependent-pair induction ----
-----------------------------------------
-----------------------------------------

mutual
  public export
  data ST0 : Type where
    ST0u : ST0
    ST0p : ST0 -> ST0 -> ST0
    ST0d : (a, b, c : ST0) -> ST1 a -> ST1 b -> ST1 c -> ST0

  public export
  data ST1 : ST0 -> Type where
    ST1u :
      (a : ST0) -> ST1 a
    ST1p :
      (a, b : ST0) -> ST1 a -> ST1 b -> ST1 (ST0p a b)
    ST1d : (a, b, c : ST0) ->
      (da : ST1 a) -> (db : ST1 b) -> (dc : ST1 c) -> ST1 (ST0d a b c da db dc)
    ST1d' : (a, b : ST0) ->
      (da : ST1 a) -> (db : ST1 b) ->
      ST1 (ST0d a a b da da db)

public export
data ST0f : (x : Type) -> SliceObj x -> Type where
  ST0fu : {x : Type} -> {f : SliceObj x} ->
    ST0f x f
  ST0fp : {x : Type} -> {f : SliceObj x} ->
    x -> x -> ST0f x f
  ST0fd : {x : Type} -> {f : SliceObj x} ->
    (a, b, c : x) -> f a -> f b -> f c -> ST0f x f

public export
ST0F_T1 : MLDirichF1_T1
ST0F_T1 = Fin 3 -- fu, fp, fd

public export
ST0F_ET1pos : SliceObj ST0F_T1
ST0F_ET1pos FZ = Void -- `fu` has no parameters
ST0F_ET1pos (FS FZ) = Fin 2 -- `fp` has 2 parameters of non-dependent type
ST0F_ET1pos (FS (FS FZ)) = Fin 3 -- `fd` has 3 parameters of non-dependent type

public export
ST0F_ET1dir : (i : ST0F_T1) -> SliceObj (ST0F_ET1pos i)
ST0F_ET1dir FZ ie1 = void ie1
ST0F_ET1dir (FS FZ) FZ = Void -- `fp` has no parameters dependent on the first
                              -- non-dependent parameter
ST0F_ET1dir (FS FZ) (FS FZ) = Void -- `fp` has no parameters dependent on the
                                   -- second non-dependent parameter
ST0F_ET1dir (FS (FS FZ)) FZ = Unit -- `fd` has one parameter dependent on the
                                   -- first non-dependent parameter
ST0F_ET1dir (FS (FS FZ)) (FS FZ) = Unit -- ditto the second parameter
ST0F_ET1dir (FS (FS FZ)) (FS (FS FZ)) = Unit -- ditto the second parameter

public export
ST0F_ET1 : MLDirichF1_ET ST0F_T1
ST0F_ET1 = (ST0F_ET1pos ** ST0F_ET1dir)

public export
ST0F_F1 : MLDirichF1
ST0F_F1 = (ST0F_T1 ** ST0F_ET1)

-- Here we show that `ST0F_F1` has an equivalent interpretation to
-- `ST0f`.

public export
ST0f_to_ET1 : (x : Type) -> (sx : SliceObj x) ->
  ST0f x sx -> InterpMLDirichF1 ST0F_F1 (x ** sx)
ST0f_to_ET1 x sx ST0fu =
  (FZ ** \v => void v ** \v => void v)
ST0f_to_ET1 x sx (ST0fp a b) =
  (FS FZ **
   flip index [a, b] **
   \i, d => case i of FZ => void d ; FS FZ => void d)
ST0f_to_ET1 x sx (ST0fd a b c da db dc) =
  (FS (FS FZ) **
   flip index [a, b, c] **
   \i, d => case i of FZ => da ; FS FZ => db ; FS (FS FZ) => dc)

public export
ST0f_from_ET1 : (x : Type) -> (sx : SliceObj x) ->
  InterpMLDirichF1 ST0F_F1 (x ** sx) -> ST0f x sx
ST0f_from_ET1 x sx (FZ ** dm1 ** dm2) =
  ST0fu
ST0f_from_ET1 x sx (FS FZ ** dm1 ** dm2) =
  ST0fp (dm1 FZ) (dm1 $ FS FZ)
ST0f_from_ET1 x sx (FS $ FS FZ ** dm1 ** dm2) =
  ST0fd
    (dm1 FZ) (dm1 $ FS FZ) (dm1 $ FS $ FS FZ)
    (dm2 FZ ()) (dm2 (FS FZ) ()) (dm2 (FS $ FS FZ) ())

public export
data ST1f : (x : Type) -> (f : SliceObj x) -> Type where
  ST1fu : {x : Type} -> {f : SliceObj x} ->
    ST1f x f
  ST1fp : {x : Type} -> {f : SliceObj x} ->
    {a, b : x} -> f a -> f b ->
    ST1f x f
  ST1fd : {x : Type} -> {f : SliceObj x} ->
    {a, b, c : x} -> f a -> f b -> f c ->
    ST1f x f
  ST1fd' : {x : Type} -> {f : SliceObj x} ->
    {a, b : x} -> f a -> f b ->
    ST1f x f

public export
ST1F_T1 : MLDirichF1_T1
ST1F_T1 = Fin 4 -- fu, fp, fd, fd'

public export
ST1F_ET1pos : SliceObj ST1F_T1
ST1F_ET1pos FZ = Void
ST1F_ET1pos (FS FZ) = Fin 2
ST1F_ET1pos (FS (FS FZ)) = Fin 3
ST1F_ET1pos (FS (FS (FS FZ))) = Fin 2

public export
ST1F_ET1dir : (i : ST1F_T1) -> SliceObj (ST1F_ET1pos i)
ST1F_ET1dir FZ ie1 = void ie1
ST1F_ET1dir (FS FZ) FZ = Unit
ST1F_ET1dir (FS FZ) (FS FZ) = Unit
ST1F_ET1dir (FS (FS FZ)) FZ = Unit
ST1F_ET1dir (FS (FS FZ)) (FS FZ) = Unit
ST1F_ET1dir (FS (FS FZ)) (FS (FS FZ)) = Unit
ST1F_ET1dir (FS (FS (FS FZ))) FZ = Unit
ST1F_ET1dir (FS (FS (FS FZ))) (FS FZ) = Unit

public export
ST1F_ET1 : MLDirichF1_ET ST1F_T1
ST1F_ET1 = (ST1F_ET1pos ** ST1F_ET1dir)

public export
ST1F_F1 : MLDirichF1
ST1F_F1 = (ST1F_T1 ** ST1F_ET1)

public export
ST1f_to_ET1 : (x : Type) -> (sx : SliceObj x) ->
  ST1f x sx -> InterpMLDirichF1 ST1F_F1 (x ** sx)
ST1f_to_ET1 x sx ST1fu =
  (FZ ** \v => void v ** \v => void v)
ST1f_to_ET1 x sx (ST1fp {a} {b} da db) =
  (FS FZ **
   flip index [a, b] **
   \i, d => case i of FZ => da; FS FZ => db)
ST1f_to_ET1 x sx (ST1fd {a} {b} {c} da db dc) =
  (FS (FS FZ) **
   flip index [a, b, c] **
   \i, d => case i of FZ => da ; FS FZ => db ; FS (FS FZ) => dc)
ST1f_to_ET1 x sx (ST1fd' {a} {b} da db) =
  (FS (FS FZ) **
   flip index [a, a, b] **
   \i, d => case i of FZ => da ; FS FZ => da ; FS (FS FZ) => db)

public export
ST1f_from_ET1 : (x : Type) -> (sx : SliceObj x) ->
  InterpMLDirichF1 ST1F_F1 (x ** sx) -> ST1f x sx
ST1f_from_ET1 x sx (FZ ** dm1 ** dm2) =
  ST1fu
ST1f_from_ET1 x sx (FS FZ ** dm1 ** dm2) =
  ST1fp {a=(dm1 FZ)} {b=(dm1 $ FS FZ)} (dm2 FZ ()) (dm2 (FS FZ) ())
ST1f_from_ET1 x sx (FS $ FS FZ ** dm1 ** dm2) =
  ST1fd (dm2 FZ ()) (dm2 (FS FZ) ()) (dm2 (FS $ FS FZ) ())
ST1f_from_ET1 x sx (FS $ FS $ FS FZ ** dm1 ** dm2) =
  ST1fd' (dm2 FZ ()) (dm2 (FS FZ) ())

public export
ST1fnt : (x : Type) -> (f : SliceObj x) -> ST1f x f -> ST0f x f
ST1fnt x f ST1fu = ST0fu {x} {f}
ST1fnt x f (ST1fp {a} {b} da db) = ST0fp {x} {f} a b
ST1fnt x f (ST1fd {a} {b} {c} da db dc) = ST0fd {x} {f} a b c da db dc
ST1fnt x f (ST1fd' {a} {b} da db) = ST0fd {x} {f} a a b da da db

public export
STntOnPos1 : ST1F_T1 -> ST0F_T1
STntOnPos1 FZ = FZ
STntOnPos1 (FS FZ) = FS FZ
STntOnPos1 (FS (FS FZ)) = FS $ FS FZ
STntOnPos1 (FS (FS (FS FZ))) = FS $ FS FZ

public export
STntOnPos2 : (i : ST1F_T1) -> ST0F_ET1pos (STntOnPos1 i) -> ST1F_ET1pos i
STntOnPos2 FZ i2 = void i2
STntOnPos2 (FS FZ) FZ = FZ
STntOnPos2 (FS FZ) (FS FZ) = FS FZ
STntOnPos2 (FS (FS FZ)) FZ = FZ
STntOnPos2 (FS (FS FZ)) (FS FZ) = FS FZ
STntOnPos2 (FS (FS FZ)) (FS (FS FZ)) = FS $ FS FZ
STntOnPos2 (FS (FS (FS FZ))) FZ = FZ
STntOnPos2 (FS (FS (FS FZ))) (FS FZ) = FZ
STntOnPos2 (FS (FS (FS FZ))) (FS (FS FZ)) = FS FZ

public export
STntOnDir : (i1 : ST1F_T1) -> (i2 : ST0F_ET1pos (STntOnPos1 i1)) ->
  ST0F_ET1dir (STntOnPos1 i1) i2 -> ST1F_ET1dir i1 (STntOnPos2 i1 i2)
STntOnDir FZ i2 d = void i2
STntOnDir (FS FZ) FZ d = void d
STntOnDir (FS FZ) (FS FZ) d = void d
STntOnDir (FS (FS FZ)) FZ () = ()
STntOnDir (FS (FS FZ)) (FS FZ) () = ()
STntOnDir (FS (FS FZ)) (FS (FS FZ)) () = ()
STntOnDir (FS (FS (FS FZ))) FZ () = ()
STntOnDir (FS (FS (FS FZ))) (FS FZ) () = ()
STntOnDir (FS (FS (FS FZ))) (FS (FS FZ)) () = ()

public export
STnt : MLDirichF1NT ST1F_F1 ST0F_F1
STnt = (STntOnPos1 ** STntOnPos2 ** STntOnDir)

public export
STf1Sl : MLDirichF1Sl ST0F_F1
STf1Sl = (ST1F_F1 ** STnt)

public export
STmlf : MLDirichF
STmlf = (ST0F_F1 ** STf1Sl)

public export
ST1ft : (x : Type) -> (f : SliceObj x) -> ST0f x f -> Type
ST1ft x f f0 = (f1 : ST1f x f ** ST1fnt x f f1 = f0)

----------------------------------
----------------------------------
---- Dependent-pair induction ----
----------------------------------
----------------------------------

T0Starter' : Type
T0Starter' = ()

T0Maker' : Type -> Type
T0Maker' = ProductMonad

T0DepMaker' : (Type, Type) -> Type
T0DepMaker' (a, b) = (a, b, b)

Test0' : (Type, Type) -> Type
Test0' (a, b) = Either T0Starter' (Either (T0Maker' a) (T0DepMaker' (a, b)))

T0DepMakerF : {t0 : Type} -> SliceObj t0 -> Type
T0DepMakerF {t0} t1 = (a : t0 ** Fin 2 -> t1 a)

T0DepMakerSPFam : SPFDataFam {b=Type} Prelude.id (const Unit)
T0DepMakerSPFam t0 = SPFD (const t0) (\u_, et0, et0' => (et0 = et0', Fin 2))

T0DepMakerFtoSPFam : {t0 : Type} -> (t1 : SliceObj t0) ->
  T0DepMakerF {t0} t1 ->
  InterpSPFData {dom=t0} {cod=Unit} (T0DepMakerSPFam t0) t1 ()
T0DepMakerFtoSPFam {t0} t1 (et0 ** t1dm) = (et0 ** \et0, (Refl, i) => t1dm i)

T0DepMakerSPFamtoF : {t0 : Type} -> (t1 : SliceObj t0) ->
  InterpSPFData {dom=t0} {cod=Unit} (T0DepMakerSPFam t0) t1 () ->
  T0DepMakerF {t0} t1
T0DepMakerSPFamtoF {t0} t1 (et0 ** t1dm) = (et0 ** \i => t1dm et0 (Refl, i))

T0FF : {t0 : Type} -> SliceObj t0 -> Type
T0FF {t0} t1 = Either Unit (Either (t0, t0) (T0DepMakerF {t0} t1))

T0SPFamPos : (t0 : Type) -> SliceObj Unit
T0SPFamPos t0 () =
  Either
    -- T0Starter
    Unit
  $ Either
    -- T0Maker
    (t0, t0)
    -- T0DepMaker
    t0

T0SPFamDir : (t0 : Type) -> SPFdirType t0 Unit (T0SPFamPos t0)
T0SPFamDir t0 () (Left ()) et0 =
  -- T0Starter
  Void
T0SPFamDir t0 () (Right (Left (et0, et1))) et2 =
  -- T0Maker
  Void
T0SPFamDir t0 () (Right (Right et0)) et0' =
  -- T0DepMaker
  (et0 = et0', Fin 2)

T0SPFam : SPFDataFam {b=Type} Prelude.id (const Unit)
T0SPFam t0 = SPFD (T0SPFamPos t0) (T0SPFamDir t0)

T0FtoSPFam : {t0 : Type} -> (t1 : SliceObj t0) ->
  T0FF {t0} t1 ->
  InterpSPFData {dom=t0} {cod=Unit} (T0SPFam t0) t1 ()
T0FtoSPFam {t0} t1 (Left ()) =
  (Left () ** \_ => voidF _)
T0FtoSPFam {t0} t1 (Right $ Left (et0, et1)) =
  (Right (Left (et0, et1)) ** \_ => voidF _)
T0FtoSPFam {t0} t1 (Right $ Right el) =
  let (el1 ** el2) = T0DepMakerFtoSPFam {t0} t1 el in
  (Right (Right el1) ** el2)

T0SPFamToF : {t0 : Type} -> (t1 : SliceObj t0) ->
  InterpSPFData {dom=t0} {cod=Unit} (T0SPFam t0) t1 () ->
  T0FF {t0} t1
T0SPFamToF {t0} t1 (Left () ** dm) =
  Left ()
T0SPFamToF {t0} t1 (Right $ Left (et0, et0') ** dm) =
  Right $ Left (et0, et0')
T0SPFamToF {t0} t1 (Right $ Right el ** dm) =
  Right $ Right (el ** \i => dm el (Refl, i))

T0NonDepSPFpos : SliceObj Unit
T0NonDepSPFpos () = Either Unit (Either Unit Unit)

T0NonDepSPFdir : SPFdirType Unit Unit T0NonDepSPFpos
T0NonDepSPFdir () (Left ()) () = Void
T0NonDepSPFdir () (Right $ Left ()) () = Fin 2
T0NonDepSPFdir () (Right $ Right ()) () = Unit

T0NonDepSPF : SPFData Unit Unit
T0NonDepSPF = SPFD T0NonDepSPFpos T0NonDepSPFdir

T0DepSPFdir : (t0 : Type) ->
  -- SPFdirType t0 Unit (InterpSPFData T0NonDepSPF (const t0))
  (ec : Unit) -> (ep : InterpSPFData T0NonDepSPF (const t0) ec) -> SliceObj t0
T0DepSPFdir t0 () (Left () ** dm) et0 = Void
T0DepSPFdir t0 () (Right $ Left () ** dm) et0 = Void
T0DepSPFdir t0 () (Right $ Right () ** dm) et0 = (dm () () = et0, Fin 2)

T0DepSPF : (t0 : Type) -> SPFData t0 Unit
T0DepSPF t0 = SPFD (InterpSPFData T0NonDepSPF (const t0)) (T0DepSPFdir t0)

DFT1 : Type
DFT1 = (pos : Type ** dir : SliceObj pos ** (ep : pos) -> SliceObj (dir ep))

InterpDFT1 : DFT1 -> (a : Type) -> SliceObj a -> Type
InterpDFT1 (pos ** dir ** depdir) a sa =
  (ep : pos **
   dm : dir ep -> a **
   SliceMorphism {a=(dir ep)} (depdir ep) (sa . dm))

DFET : DFT1 -> Type
DFET (pos ** dir ** depdir) =
  (pos2 : Type **
   dir2 : SliceObj pos2 **
   (ep2 : pos2) -> dir2 ep2 -> ?DFET_hole)

InterpDFET : (t1 : DFT1) -> DFET t1 -> (a : Type) -> (sa : SliceObj a) ->
  SliceObj (InterpDFT1 t1 a sa)
InterpDFET (pos ** dir ** depdir) (pos2 ** dir2 ** dfet)
  a sa (ep ** dm ** ddm) =
    (esp : pos2 ** ?InterpDFET_hole)

TestPRAT1pos : Unit -> Type
TestPRAT1pos _ = Fin 3 -- T0Starter, T0Maker, T0DepMaker

TestPRAT1dir : (u : Unit) -> TestPRAT1pos u -> Unit -> Type
TestPRAT1dir () FZ () = Fin 2 -- T1Starter, T1Id
TestPRAT1dir () (FS FZ) () = Fin 4 -- T1Maker, T1Id, T1Composer, T1Distrib
TestPRAT1dir () (FS (FS FZ)) () = Fin 3 -- T1Id, T1DepComposer, T1Telescope

TestPRAT1 : MlDirichSlObj MLDirichCatObjTerminal
TestPRAT1 = MDSobj TestPRAT1pos TestPRAT1dir

TestPRAdirPos : SliceObj (Unit, Sigma {a=Unit} TestPRAT1pos)
TestPRAdirPos ((), (() ** FZ)) = ?TestPRAdirPos_hole_0
TestPRAdirPos ((), (() ** (FS FZ))) = ?TestPRAdirPos_hole_1
TestPRAdirPos ((), (() ** (FS (FS FZ)))) = ?TestPRAdirPos_hole_2

TestPRAdirDir :
  (i : (Unit, Sigma {a=Unit} TestPRAT1pos)) ->
  TestPRAdirPos i ->
  SliceObj (Unit, (u : Unit ** TestPRAT1dir (fst $ snd i) (snd $ snd i) u))
-- TestPRAdirDir ((), (() ** i)) j k = ?TestPRAdirDir_hole

TestPRAdir : PRAdirType MLDirichCatObjTerminal MLDirichCatObjTerminal TestPRAT1
TestPRAdir = MDSobj TestPRAdirPos TestPRAdirDir

TestPRA : PRAData MLDirichCatObjTerminal MLDirichCatObjTerminal
TestPRA = PRAD TestPRAT1 TestPRAdir

---------------------------------------
---------------------------------------
---- A lawful isomorphism of types ----
---------------------------------------
---------------------------------------

-- `IdrisCategories` has the predicate half of this (`ExtInverse`), but
-- no bundle; the four-field record is what the proofs below want.
public export
record TIso (0 a, b : Type) where
  constructor MkTIso
  tiTo : a -> b
  tiFrom : b -> a
  tiFromTo : (x : a) -> tiFrom (tiTo x) = x
  tiToFrom : (y : b) -> tiTo (tiFrom y) = y

public export
tisoTrans : {0 a, b, c : Type} -> TIso a b -> TIso b c -> TIso a c
tisoTrans i j =
  MkTIso
    (tiTo j . tiTo i)
    (tiFrom i . tiFrom j)
    (\x => trans (cong (tiFrom i) (tiFromTo j (tiTo i x))) (tiFromTo i x))
    (\z => trans (cong (tiTo j) (tiToFrom i (tiFrom j z))) (tiToFrom j z))


---------------------------
---------------------------
---- Equality plumbing ----
---------------------------
---------------------------

-- Transporting a fibre element backwards along `p` and repairing the
-- base element recovers the original dependent pair.
public export
dpSymReplaceEq : {0 a : Type} -> {0 b : a -> Type} -> {0 x, x' : a} ->
  (p : x' = x) -> (y : b x) ->
  MkDPair {p=b} x' (replace {p=b} (sym p) y) = MkDPair {p=b} x y
dpSymReplaceEq Refl _ = Refl

-- The same, but where the base equality is available only after
-- applying `g`, so the transport proof `r` need not be the one we hold:
-- matching it against `Refl` is the UIP step which identifies them.
public export
dpCongEq : {0 a, a' : Type} -> {0 g : a' -> a} -> {0 b : a -> Type} ->
  {0 w, w' : a'} -> (q : w' = w) -> (r : g w' = g w) -> (z : b (g w)) ->
  MkDPair {p=(\v => b (g v))} w' (replace {p=b} (sym r) z) =
    MkDPair {p=(\v => b (g v))} w z
dpCongEq Refl Refl _ = Refl

public export
replaceApp : {0 a : Type} -> {0 b : a -> Type} -> {0 x, x' : a} ->
  (p : x' = x) -> (g : (w : a) -> b w) -> replace {p=b} p (g x') = g x
replaceApp Refl _ = Refl

public export
replaceCongApp : {0 a, a' : Type} -> {0 g : a' -> a} ->
  {0 b : a -> Type} -> {0 w, w' : a'} ->
  (q : w' = w) -> (r : g w' = g w) -> (h : (v : a') -> b (g v)) ->
  replace {p=b} r (h w') = h w
replaceCongApp Refl Refl _ = Refl

-- A dependent sum is determined by its base and its fibres, so an
-- equality of bases plus a fibrewise equality gives an equality of
-- sums.  (`funExt` is what turns the fibrewise data into one
-- equality of families.)
public export
sigmaTyCong : FunExt -> {a, a' : Type} -> (p : a' = a) ->
  (b : a -> Type) -> (b' : a' -> Type) ->
  ((x : a') -> b' x = b (replace {p=(\t => t)} p x)) ->
  Sigma {a=a'} b' = Sigma {a} b
sigmaTyCong fext Refl b b' q = cong (Sigma {a}) (funExt q)

public export
piTyCong : FunExt -> {a, a' : Type} -> (p : a' = a) ->
  (b : a -> Type) -> (b' : a' -> Type) ->
  ((x : a') -> b' x = b (replace {p=(\t => t)} p x)) ->
  Pi {a=a'} b' = Pi {a} b
piTyCong fext Refl b b' q = cong (Pi {a}) (funExt q)


----------------------------------------------------------
----------------------------------------------------------
---- Dependent sums and products along an isomorphism ----
----------------------------------------------------------
----------------------------------------------------------

public export
sigmaCongFrom : {0 a, a' : Type} -> (i : TIso a a') -> (0 b : a -> Type) ->
  TIso (Sigma {a} b) (Sigma {a=a'} (\w => b (tiFrom i w)))
sigmaCongFrom i b =
  MkTIso
    (\x =>
      MkDPair {p=(\w => b (tiFrom i w))} (tiTo i (fst x))
        (replace {p=b} (sym (tiFromTo i (fst x))) (snd x)))
    (\z => MkDPair {p=b} (tiFrom i (fst z)) (snd z))
    (\x =>
      trans
        (dpSymReplaceEq {b} (tiFromTo i (fst x)) (snd x))
        (sym $ dpEqPat {p=b} {dp=x}))
    (\z =>
      trans
        (dpCongEq {g=(tiFrom i)} {b}
          (tiToFrom i (fst z)) (tiFromTo i (tiFrom i (fst z))) (snd z))
        (sym $ dpEqPat {p=(\w => b (tiFrom i w))} {dp=z}))

public export
piCongFrom : FunExt -> {0 a, a' : Type} -> (i : TIso a a') ->
  (0 b : a -> Type) ->
  TIso (Pi {a} b) (Pi {a=a'} (\w => b (tiFrom i w)))
piCongFrom fext i b =
  MkTIso
    (\g, w => g (tiFrom i w))
    (\h, x => replace {p=b} (tiFromTo i x) (h (tiTo i x)))
    (\g => funExt $ \x => replaceApp {b} (tiFromTo i x) g)
    (\h =>
      funExt $ \w =>
        replaceCongApp {g=(tiFrom i)} {b}
          (tiToFrom i w) (tiFromTo i (tiFrom i w)) h)


-- The universe is generated by a family of starting types `sty`,
-- indexed by `idx`.  Everything below is parameterized by that
-- family; the original formulation is the case `idx = Unit`,
-- `sty () = Nat`.
parameters (idx : Type) (sty : idx -> Type)
  ---------------------------------------------------
  ---------------------------------------------------
  ---- The universe endofunctor on families ----
  ---------------------------------------------------
  ---------------------------------------------------

  -- Objects of the base category:  a type of codes together with a
  -- decoding of them.  (`FreeCoprodCompDisc Type` in the Lean.)
  public export
  IRFam : Type
  IRFam = (ty : Type ** ty -> Type)

  -- Morphisms are maps of codes which *preserve* the decoding:  the
  -- base is discrete.  That discreteness is what makes the decoding's
  -- negative occurrence in `IRUnivPos` harmless, and so what makes
  -- `IRUniv` a functor at all.
  public export
  IRFamMor : IRFam -> IRFam -> Type
  IRFamMor o o' = (g : fst o -> fst o' ** ExtEq (snd o' . g) (snd o))

  -- The first component of the endofunctor, a map to `Type`:  the
  -- codes of the next stage -- one starting type per index, a
  -- dependent-sum former, and a dependent-product former.
  public export
  IRUnivPos : IRFam -> Type
  IRUnivPos o =
    Either idx
      (Either
        (u : fst o ** (snd o u -> fst o))
        (u : fst o ** (snd o u -> fst o)))

  -- The second component, dependent on the output of the first:  the
  -- decoding of each new code.
  public export
  IRUnivDec : (o : IRFam) -> IRUnivPos o -> Type
  IRUnivDec o (Left i) = sty i
  IRUnivDec o (Right (Left (u ** f))) = Sigma {a=(snd o u)} (snd o . f)
  IRUnivDec o (Right (Right (u ** f))) = Pi {a=(snd o u)} (snd o . f)

  -- The endofunctor is the dependent pair of the two components.
  public export
  IRUniv : IRFam -> IRFam
  IRUniv o = (IRUnivPos o ** IRUnivDec o)

  ---- The action of `IRUniv` on morphisms ----

  -- On codes:  rename the bound code, and reindex the family under
  -- the binder.  Reindexing needs the decoding to travel *backwards*
  -- along the morphism, which is exactly what discreteness supplies.
  public export
  IRUnivPosMor : (o, o' : IRFam) -> (m : IRFamMor o o') ->
    IRUnivPos o -> IRUnivPos o'
  IRUnivPosMor o o' m (Left i) = Left i
  IRUnivPosMor o o' m (Right (Left (u ** f))) =
    Right (Left
      (fst m u ** \x => fst m (f (replace {p=(\t => t)} (snd m u) x))))
  IRUnivPosMor o o' m (Right (Right (u ** f))) =
    Right (Right
      (fst m u ** \x => fst m (f (replace {p=(\t => t)} (snd m u) x))))

  -- ... and the renaming preserves the decoding, which is what makes
  -- it a morphism of the target family.
  public export
  IRUnivDecMor : FunExt -> (o, o' : IRFam) -> (m : IRFamMor o o') ->
    ExtEq (IRUnivDec o' . IRUnivPosMor o o' m) (IRUnivDec o)
  IRUnivDecMor fext o o' m (Left i) = Refl
  IRUnivDecMor fext o o' m (Right (Left (u ** f))) =
    sigmaTyCong fext (snd m u) (snd o . f)
      (snd o' . (\x => fst m (f (replace {p=(\t => t)} (snd m u) x))))
      (\x => snd m (f (replace {p=(\t => t)} (snd m u) x)))
  IRUnivDecMor fext o o' m (Right (Right (u ** f))) =
    piTyCong fext (snd m u) (snd o . f)
      (snd o' . (\x => fst m (f (replace {p=(\t => t)} (snd m u) x))))
      (\x => snd m (f (replace {p=(\t => t)} (snd m u) x)))

  -- The morphism map of the endofunctor, again a dependent pair of
  -- the two components.  The functor laws are not proved here.
  public export
  IRUnivMor : FunExt -> (o, o' : IRFam) -> (m : IRFamMor o o') ->
    IRFamMor (IRUniv o) (IRUniv o')
  IRUnivMor fext o o' m = (IRUnivPosMor o o' m ** IRUnivDecMor fext o o' m)

  -- The initial algebra.  `IRCode` and `IRdecode` are the components
  -- of the least fixed point of `IRUniv`, in the style of `Mu`, but
  -- over families rather than over `Type`.  Idris accepts `IRCode`
  -- itself, but can no longer see that `IRdecode` terminates:  the
  -- recursive calls are hidden inside `IRUnivDec`.
  mutual
    public export
    data IRCode : Type where
      InIRC : IRUnivPos (IRCode ** IRdecode) -> IRCode

    public export
    partial
    IRdecode : IRCode -> Type
    IRdecode (InIRC p) = IRUnivDec (IRCode ** IRdecode) p

  -- The former data constructors, now smart constructors.  Building a
  -- code is unchanged; matching on one must go through `InIRC`.
  public export
  IRCiota : (i : idx) -> IRCode
  IRCiota i = InIRC (Left i)

  public export
  partial
  IRCsigma : (u : IRCode) -> (IRdecode u -> IRCode) -> IRCode
  IRCsigma u f = InIRC (Right (Left (u ** f)))

  public export
  partial
  IRCpi : (u : IRCode) -> (IRdecode u -> IRCode) -> IRCode
  IRCpi u f = InIRC (Right (Right (u ** f)))

  -------------------------------------------
  -------------------------------------------
  ---- The universe endofunctor on arrows ----
  -------------------------------------------
  -------------------------------------------

  -- Objects of the base category:  a map, read as the fibration whose
  -- fibre over a code is the type of terms of that code.
  public export
  IRArr : Type
  IRArr = (dom : Type ** (cod : Type ** (dom -> cod)))

  public export
  IRArrDom : IRArr -> Type
  IRArrDom o = fst o

  public export
  IRArrCod : IRArr -> Type
  IRArrCod o = fst (snd o)

  public export
  IRArrPrj : (o : IRArr) -> IRArrDom o -> IRArrCod o
  IRArrPrj o = snd (snd o)

  public export
  IRArrFib : (o : IRArr) -> IRArrCod o -> Type
  IRArrFib o c = (t : IRArrDom o ** IRArrPrj o t = c)

  -- An arrow and a family carry the same information:  a fibration is
  -- its family of fibres.  Under that translation the arrow functor's
  -- two components are *literally* the family functor's -- the
  -- definitions below are by `IRUnivPos`/`IRUnivDec` on the
  -- translated family, not merely isomorphic to them.  This is the
  -- sense in which the inductive-recursive and inductive-inductive
  -- formulations are two readings of one endofunctor:  the decoding
  -- lands in `Type` in one and in the codes themselves in the other.
  public export
  IRArrToFam : IRArr -> IRFam
  IRArrToFam o = (IRArrCod o ** IRArrFib o)

  public export
  IRArrPos : IRArr -> Type
  IRArrPos o = IRUnivPos (IRArrToFam o)

  public export
  IRArrTm : (o : IRArr) -> IRArrPos o -> Type
  IRArrTm o = IRUnivDec (IRArrToFam o)

  -- The new domain is the total space of the terms and the new
  -- projection is its first component, so the arrow of the image is a
  -- plain first projection.
  public export
  IRArrF : IRArr -> IRArr
  IRArrF o = (Sigma {a=(IRArrPos o)} (IRArrTm o) ** (IRArrPos o ** fst))

  -- The initial algebra, again in the style of `Mu`.  Here Idris
  -- accepts even `IRTerm` and `IRCode'` without `partial`:  the
  -- negative occurrence which the direct formulation exposed is now
  -- hidden behind `IRArrPos`, so the positivity check simply cannot
  -- see it.  That is a weaker check, not a stronger guarantee.
  mutual
    public export
    data IRTerm : Type where
      InIRT :
        Sigma {a=(IRArrPos (IRTerm ** (IRCode' ** IRfib)))}
          (IRArrTm (IRTerm ** (IRCode' ** IRfib))) -> IRTerm

    public export
    data IRCode' : Type where
      InIRC' : IRArrPos (IRTerm ** (IRCode' ** IRfib)) -> IRCode'

    public export
    partial
    IRfib : IRTerm -> IRCode'
    IRfib (InIRT (c ** _)) = InIRC' c

  -------------------------------
  -------------------------------
  ---- The fibres of `IRfib` ----
  -------------------------------
  -------------------------------

  -- The fibre of `IRfib` over a code:  the terms which `IRfib` assigns
  -- that code.  This is the inductive-inductive formulation's stand-in
  -- for the inductive-recursive formulation's `IRdecode`.
  public export
  partial
  IRFib : IRCode' -> Type
  IRFib u = (t : IRTerm ** IRfib t = u)

  ------------------------------------------------
  ------------------------------------------------
  ---- Smart constructors for codes and terms ----
  ------------------------------------------------
  ------------------------------------------------

  public export
  partial
  IRCiota' : (i : idx) -> IRCode'
  IRCiota' i = InIRC' (Left i)

  public export
  partial
  IRCsigma' : (u : IRCode') -> (IRFib u -> IRCode') -> IRCode'
  IRCsigma' u v = InIRC' (Right (Left (u ** v)))

  public export
  partial
  IRCpi' : (u : IRCode') -> (IRFib u -> IRCode') -> IRCode'
  IRCpi' u v = InIRC' (Right (Right (u ** v)))

  public export
  partial
  IRTiota : (i : idx) -> sty i -> IRTerm
  IRTiota i n = InIRT (Left i ** n)

  -- The dependent-sum and dependent-product term formers now take
  -- fibre elements directly, rather than a term paired with a proof.
  public export
  partial
  IRTsigma : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (x : IRFib u) -> IRFib (v x) -> IRTerm
  IRTsigma u v x y = InIRT (Right (Left (u ** v)) ** (x ** y))

  public export
  partial
  IRTpi : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    ((x : IRFib u) -> IRFib (v x)) -> IRTerm
  IRTpi u v g = InIRT (Right (Right (u ** v)) ** g)


  ----------------------------------------------
  ----------------------------------------------
  ---- The fibre over a starting-type code ----
  ----------------------------------------------
  ----------------------------------------------

  public export
  partial
  iotaFibTo : (i : idx) -> sty i -> IRFib (IRCiota' i)
  iotaFibTo i n = (IRTiota i n ** Refl)

  public export
  partial
  iotaFibFrom : (i : idx) -> IRFib (IRCiota' i) -> sty i
  iotaFibFrom i (InIRT (_ ** n) ** Refl) = n

  public export
  partial
  iotaFibToFrom : (i : idx) -> (z : IRFib (IRCiota' i)) ->
    iotaFibTo i (iotaFibFrom i z) = z
  iotaFibToFrom i (InIRT (_ ** _) ** Refl) = Refl

  public export
  partial
  iotaFibIso : (i : idx) -> TIso (sty i) (IRFib (IRCiota' i))
  iotaFibIso i =
    MkTIso (iotaFibTo i) (iotaFibFrom i) (\_ => Refl) (iotaFibToFrom i)


  ---------------------------------------------
  ---------------------------------------------
  ---- The fibre over a dependent-sum code ----
  ---------------------------------------------
  ---------------------------------------------

  public export
  partial
  sigmaPair : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (x : IRFib u) -> IRFib (v x) -> IRFib (IRCsigma' u v)
  sigmaPair u v x y = (IRTsigma u v x y ** Refl)

  -- Matching the equality proof against `Refl` is what inverts the
  -- constructor:  it forces the (higher-order) index `v` as well as `u`.
  public export
  partial
  sigmaFst : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    IRFib (IRCsigma' u v) -> IRFib u
  sigmaFst u v (InIRT (_ ** tm) ** Refl) = fst tm

  public export
  partial
  sigmaSnd : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (z : IRFib (IRCsigma' u v)) -> IRFib (v (sigmaFst u v z))
  sigmaSnd u v (InIRT (_ ** tm) ** Refl) = snd tm

  public export
  partial
  sigmaEta : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (z : IRFib (IRCsigma' u v)) ->
    sigmaPair u v (sigmaFst u v z) (sigmaSnd u v z) = z
  sigmaEta u v (InIRT (_ ** (_ ** _)) ** Refl) = Refl

  public export
  partial
  sigmaFibTo : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (0 b : IRFib u -> Type) ->
    (j : (w : IRFib u) -> TIso (b w) (IRFib (v w))) ->
    Sigma {a=(IRFib u)} b -> IRFib (IRCsigma' u v)
  sigmaFibTo u v b j x = sigmaPair u v (fst x) (tiTo (j (fst x)) (snd x))

  public export
  partial
  sigmaFibFrom : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (0 b : IRFib u -> Type) ->
    (j : (w : IRFib u) -> TIso (b w) (IRFib (v w))) ->
    IRFib (IRCsigma' u v) -> Sigma {a=(IRFib u)} b
  sigmaFibFrom u v b j z =
    MkDPair {p=b} (sigmaFst u v z)
      (tiFrom (j (sigmaFst u v z)) (sigmaSnd u v z))

  public export
  partial
  sigmaFibFromPair : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (0 b : IRFib u -> Type) ->
    (j : (w : IRFib u) -> TIso (b w) (IRFib (v w))) ->
    (x : IRFib u) -> (y : IRFib (v x)) ->
    sigmaFibFrom u v b j (sigmaPair u v x y) =
      MkDPair {p=b} x (tiFrom (j x) y)
  sigmaFibFromPair u v b j _ _ = Refl

  public export
  partial
  sigmaFibFromTo : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (0 b : IRFib u -> Type) ->
    (j : (w : IRFib u) -> TIso (b w) (IRFib (v w))) ->
    (x : Sigma {a=(IRFib u)} b) ->
    sigmaFibFrom u v b j (sigmaFibTo u v b j x) = x
  sigmaFibFromTo u v b j x =
    trans
      (sigmaFibFromPair u v b j (fst x) (tiTo (j (fst x)) (snd x)))
      (trans
        (cong (MkDPair {p=b} (fst x)) (tiFromTo (j (fst x)) (snd x)))
        (sym $ dpEqPat {p=b} {dp=x}))

  public export
  partial
  sigmaFibToFrom : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (0 b : IRFib u -> Type) ->
    (j : (w : IRFib u) -> TIso (b w) (IRFib (v w))) ->
    (z : IRFib (IRCsigma' u v)) ->
    sigmaFibTo u v b j (sigmaFibFrom u v b j z) = z
  sigmaFibToFrom u v b j z =
    trans
      (cong (sigmaPair u v (sigmaFst u v z))
        (tiToFrom (j (sigmaFst u v z)) (sigmaSnd u v z)))
      (sigmaEta u v z)

  public export
  partial
  sigmaFibIso : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (0 b : IRFib u -> Type) ->
    (j : (w : IRFib u) -> TIso (b w) (IRFib (v w))) ->
    TIso (Sigma {a=(IRFib u)} b) (IRFib (IRCsigma' u v))
  sigmaFibIso u v b j =
    MkTIso (sigmaFibTo u v b j) (sigmaFibFrom u v b j)
      (sigmaFibFromTo u v b j) (sigmaFibToFrom u v b j)


  -------------------------------------------------
  -------------------------------------------------
  ---- The fibre over a dependent-product code ----
  -------------------------------------------------
  -------------------------------------------------

  public export
  partial
  piLam : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    ((x : IRFib u) -> IRFib (v x)) -> IRFib (IRCpi' u v)
  piLam u v g = (IRTpi u v g ** Refl)

  public export
  partial
  piApp : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    IRFib (IRCpi' u v) -> (x : IRFib u) -> IRFib (v x)
  piApp u v (InIRT (_ ** tm) ** Refl) = tm

  public export
  partial
  piBeta : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (g : (x : IRFib u) -> IRFib (v x)) -> (x : IRFib u) ->
    piApp u v (piLam u v g) x = g x
  piBeta u v g _ = Refl

  public export
  partial
  piEta : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (h : IRFib (IRCpi' u v)) -> piLam u v (piApp u v h) = h
  piEta u v (InIRT (_ ** _) ** Refl) = Refl

  public export
  partial
  piFibTo : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (0 b : IRFib u -> Type) ->
    (j : (w : IRFib u) -> TIso (b w) (IRFib (v w))) ->
    Pi {a=(IRFib u)} b -> IRFib (IRCpi' u v)
  piFibTo u v b j g = piLam u v (\w => tiTo (j w) (g w))

  public export
  partial
  piFibFrom : (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (0 b : IRFib u -> Type) ->
    (j : (w : IRFib u) -> TIso (b w) (IRFib (v w))) ->
    IRFib (IRCpi' u v) -> Pi {a=(IRFib u)} b
  piFibFrom u v b j h w = tiFrom (j w) (piApp u v h w)

  public export
  partial
  piFibFromTo : FunExt -> (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (0 b : IRFib u -> Type) ->
    (j : (w : IRFib u) -> TIso (b w) (IRFib (v w))) ->
    (g : Pi {a=(IRFib u)} b) ->
    piFibFrom u v b j (piFibTo u v b j g) = g
  piFibFromTo fext u v b j g =
    funExt $ \w =>
      trans
        (cong (tiFrom (j w)) (piBeta u v (\w' => tiTo (j w') (g w')) w))
        (tiFromTo (j w) (g w))

  public export
  partial
  piFibToFrom : FunExt -> (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (0 b : IRFib u -> Type) ->
    (j : (w : IRFib u) -> TIso (b w) (IRFib (v w))) ->
    (h : IRFib (IRCpi' u v)) ->
    piFibTo u v b j (piFibFrom u v b j h) = h
  piFibToFrom fext u v b j h =
    trans
      (cong (piLam u v)
        (funExt {f=(\w => tiTo (j w) (tiFrom (j w) (piApp u v h w)))}
                {g=(piApp u v h)}
          (\w => tiToFrom (j w) (piApp u v h w))))
      (piEta u v h)

  public export
  partial
  piFibIso : FunExt -> (u : IRCode') -> (v : IRFib u -> IRCode') ->
    (0 b : IRFib u -> Type) ->
    (j : (w : IRFib u) -> TIso (b w) (IRFib (v w))) ->
    TIso (Pi {a=(IRFib u)} b) (IRFib (IRCpi' u v))
  piFibIso fext u v b j =
    MkTIso (piFibTo u v b j) (piFibFrom u v b j)
      (piFibFromTo fext u v b j) (piFibToFrom fext u v b j)


  -------------------------------------------------------
  -------------------------------------------------------
  ---- The translation, and the decoding isomorphism ----
  -------------------------------------------------------
  -------------------------------------------------------

  -- `IRtoC` translates an inductive-recursive code to an
  -- inductive-inductive one, and `IRdecIso` simultaneously exhibits the
  -- decoding of a code as the fibre of `IRfib` over its translation.
  -- The two must be defined together:  translating `IRCsigma u f`
  -- requires reindexing `f` along the inverse of the isomorphism at `u`.
  mutual
    public export
    partial
    IRtoC : FunExt -> IRCode -> IRCode'
    IRtoC fext (InIRC (Left i)) = IRCiota' i
    IRtoC fext (InIRC (Right (Left (u ** f)))) =
      IRCsigma' (IRtoC fext u)
        (\w => IRtoC fext (f (tiFrom (IRdecIso fext u) w)))
    IRtoC fext (InIRC (Right (Right (u ** f)))) =
      IRCpi' (IRtoC fext u)
        (\w => IRtoC fext (f (tiFrom (IRdecIso fext u) w)))

    public export
    partial
    IRdecIso : (fext : FunExt) -> (u : IRCode) ->
      TIso (IRdecode u) (IRFib (IRtoC fext u))
    IRdecIso fext (InIRC (Left i)) = iotaFibIso i
    IRdecIso fext (InIRC (Right (Left (u ** f)))) =
      tisoTrans
        (sigmaCongFrom (IRdecIso fext u) (\x => IRdecode (f x)))
        (sigmaFibIso
          (IRtoC fext u)
          (\w => IRtoC fext (f (tiFrom (IRdecIso fext u) w)))
          (\w => IRdecode (f (tiFrom (IRdecIso fext u) w)))
          (\w => IRdecIso fext (f (tiFrom (IRdecIso fext u) w))))
    IRdecIso fext (InIRC (Right (Right (u ** f)))) =
      tisoTrans
        (piCongFrom fext (IRdecIso fext u) (\x => IRdecode (f x)))
        (piFibIso fext
          (IRtoC fext u)
          (\w => IRtoC fext (f (tiFrom (IRdecIso fext u) w)))
          (\w => IRdecode (f (tiFrom (IRdecIso fext u) w)))
          (\w => IRdecIso fext (f (tiFrom (IRdecIso fext u) w))))


  ---------------------------------------------------------------
  ---------------------------------------------------------------
  ---- Disjointness and injectivity of the code constructors ----
  ---------------------------------------------------------------
  ---------------------------------------------------------------

  public export
  partial
  isIotaC : IRCode' -> Bool
  isIotaC (InIRC' (Left _)) = True
  isIotaC (InIRC' (Right (Left _))) = False
  isIotaC (InIRC' (Right (Right _))) = False

  public export
  partial
  isSigmaC : IRCode' -> Bool
  isSigmaC (InIRC' (Left _)) = False
  isSigmaC (InIRC' (Right (Left _))) = True
  isSigmaC (InIRC' (Right (Right _))) = False

  public export
  partial
  iotaCodeInj : (i1, i2 : idx) -> IRCiota' i1 = IRCiota' i2 -> i1 = i2
  iotaCodeInj _ _ Refl = Refl

  public export
  partial
  sigmaCodeInjFst : (a1 : IRCode') -> (v1 : IRFib a1 -> IRCode') ->
    (a2 : IRCode') -> (v2 : IRFib a2 -> IRCode') ->
    IRCsigma' a1 v1 = IRCsigma' a2 v2 -> a1 = a2
  sigmaCodeInjFst _ _ _ _ Refl = Refl

  public export
  partial
  sigmaCodeInjSnd : (a1 : IRCode') -> (v1 : IRFib a1 -> IRCode') ->
    (a2 : IRCode') -> (v2 : IRFib a2 -> IRCode') ->
    (p : IRCsigma' a1 v1 = IRCsigma' a2 v2) -> (w : IRFib a1) ->
    v1 w = v2 (replace {p=IRFib} (sigmaCodeInjFst a1 v1 a2 v2 p) w)
  sigmaCodeInjSnd _ _ _ _ Refl _ = Refl

  public export
  partial
  piCodeInjFst : (a1 : IRCode') -> (v1 : IRFib a1 -> IRCode') ->
    (a2 : IRCode') -> (v2 : IRFib a2 -> IRCode') ->
    IRCpi' a1 v1 = IRCpi' a2 v2 -> a1 = a2
  piCodeInjFst _ _ _ _ Refl = Refl

  public export
  partial
  piCodeInjSnd : (a1 : IRCode') -> (v1 : IRFib a1 -> IRCode') ->
    (a2 : IRCode') -> (v2 : IRFib a2 -> IRCode') ->
    (p : IRCpi' a1 v1 = IRCpi' a2 v2) -> (w : IRFib a1) ->
    v1 w = v2 (replace {p=IRFib} (piCodeInjFst a1 v1 a2 v2 p) w)
  piCodeInjSnd _ _ _ _ Refl _ = Refl


  -----------------------------------------------
  -----------------------------------------------
  ---- Congruences for the code constructors ----
  -----------------------------------------------
  -----------------------------------------------

  public export
  partial
  sigmaCodeCong : FunExt -> (a1 : IRCode') -> (v1 : IRFib a1 -> IRCode') ->
    (a2 : IRCode') -> (v2 : IRFib a2 -> IRCode') -> (p : a1 = a2) ->
    ((w : IRFib a1) -> v1 w = v2 (replace {p=IRFib} p w)) ->
    IRCsigma' a1 v1 = IRCsigma' a2 v2
  sigmaCodeCong fext a v1 a v2 Refl q = cong (IRCsigma' a) (funExt q)

  public export
  partial
  piCodeCong : FunExt -> (a1 : IRCode') -> (v1 : IRFib a1 -> IRCode') ->
    (a2 : IRCode') -> (v2 : IRFib a2 -> IRCode') -> (p : a1 = a2) ->
    ((w : IRFib a1) -> v1 w = v2 (replace {p=IRFib} p w)) ->
    IRCpi' a1 v1 = IRCpi' a2 v2
  piCodeCong fext a v1 a v2 Refl q = cong (IRCpi' a) (funExt q)

  public export
  partial
  IRCsigmaCong : FunExt -> (u1 : IRCode) -> (f1 : IRdecode u1 -> IRCode) ->
    (u2 : IRCode) -> (f2 : IRdecode u2 -> IRCode) -> (p : u1 = u2) ->
    ((x : IRdecode u1) -> f1 x = f2 (replace {p=IRdecode} p x)) ->
    IRCsigma u1 f1 = IRCsigma u2 f2
  IRCsigmaCong fext u f1 u f2 Refl q = cong (IRCsigma u) (funExt q)

  public export
  partial
  IRCpiCong : FunExt -> (u1 : IRCode) -> (f1 : IRdecode u1 -> IRCode) ->
    (u2 : IRCode) -> (f2 : IRdecode u2 -> IRCode) -> (p : u1 = u2) ->
    ((x : IRdecode u1) -> f1 x = f2 (replace {p=IRdecode} p x)) ->
    IRCpi u1 f1 = IRCpi u2 f2
  IRCpiCong fext u f1 u f2 Refl q = cong (IRCpi u) (funExt q)


  ------------------------------
  ------------------------------
  ---- A section of `IRtoC` ----
  ------------------------------
  ------------------------------

  -- `IRcodeInv` picks, for each inductive-inductive code, an
  -- inductive-recursive code translating to it; `IRcodeInvEq` is the
  -- proof.  Together they say that `IRtoC` is (split) surjective.
  mutual
    public export
    partial
    IRcodeInv : FunExt -> IRCode' -> IRCode
    IRcodeInv fext (InIRC' (Left i)) = IRCiota i
    IRcodeInv fext (InIRC' (Right (Left (a ** v)))) =
      IRCsigma (IRcodeInv fext a)
        (\x => IRcodeInv fext
          (v (replace {p=IRFib} (IRcodeInvEq fext a)
               (tiTo (IRdecIso fext (IRcodeInv fext a)) x))))
    IRcodeInv fext (InIRC' (Right (Right (a ** v)))) =
      IRCpi (IRcodeInv fext a)
        (\x => IRcodeInv fext
          (v (replace {p=IRFib} (IRcodeInvEq fext a)
               (tiTo (IRdecIso fext (IRcodeInv fext a)) x))))

    public export
    partial
    IRcodeInvEq : (fext : FunExt) -> (a : IRCode') ->
      IRtoC fext (IRcodeInv fext a) = a
    IRcodeInvEq fext (InIRC' (Left i)) = Refl
    IRcodeInvEq fext (InIRC' (Right (Left (a ** v)))) =
      sigmaCodeCong fext
        (IRtoC fext (IRcodeInv fext a))
        (\w => IRtoC fext
          (IRcodeInv fext
            (v (replace {p=IRFib} (IRcodeInvEq fext a)
                 (tiTo (IRdecIso fext (IRcodeInv fext a))
                   (tiFrom (IRdecIso fext (IRcodeInv fext a)) w))))))
        a v
        (IRcodeInvEq fext a)
        (\w =>
          trans
            (IRcodeInvEq fext
              (v (replace {p=IRFib} (IRcodeInvEq fext a)
                   (tiTo (IRdecIso fext (IRcodeInv fext a))
                     (tiFrom (IRdecIso fext (IRcodeInv fext a)) w)))))
            (cong (\w' => v (replace {p=IRFib} (IRcodeInvEq fext a) w'))
              (tiToFrom (IRdecIso fext (IRcodeInv fext a)) w)))
    IRcodeInvEq fext (InIRC' (Right (Right (a ** v)))) =
      piCodeCong fext
        (IRtoC fext (IRcodeInv fext a))
        (\w => IRtoC fext
          (IRcodeInv fext
            (v (replace {p=IRFib} (IRcodeInvEq fext a)
                 (tiTo (IRdecIso fext (IRcodeInv fext a))
                   (tiFrom (IRdecIso fext (IRcodeInv fext a)) w))))))
        a v
        (IRcodeInvEq fext a)
        (\w =>
          trans
            (IRcodeInvEq fext
              (v (replace {p=IRFib} (IRcodeInvEq fext a)
                   (tiTo (IRdecIso fext (IRcodeInv fext a))
                     (tiFrom (IRdecIso fext (IRcodeInv fext a)) w)))))
            (cong (\w' => v (replace {p=IRFib} (IRcodeInvEq fext a) w'))
              (tiToFrom (IRdecIso fext (IRcodeInv fext a)) w)))


  ------------------------------
  ------------------------------
  ---- `IRtoC` is injective ----
  ------------------------------
  ------------------------------

  -- The decoding isomorphisms are coherent with any equality of codes:
  -- transporting a decoding along `pu` agrees with transporting the
  -- corresponding fibre element along `pc`.  The two proofs need not be
  -- related a priori -- matching both against `Refl` is the UIP step
  -- which identifies them.
  public export
  partial
  IRdecIsoCoh : (fext : FunExt) -> (u1, u2 : IRCode) -> (pu : u1 = u2) ->
    (pc : IRtoC fext u1 = IRtoC fext u2) -> (x : IRdecode u1) ->
    tiFrom (IRdecIso fext u2)
      (replace {p=IRFib} pc (tiTo (IRdecIso fext u1) x)) =
        replace {p=IRdecode} pu x
  IRdecIsoCoh fext u u Refl Refl x = tiFromTo (IRdecIso fext u) x

  mutual
    public export
    partial
    IRtoCinj : (fext : FunExt) -> (u1, u2 : IRCode) ->
      IRtoC fext u1 = IRtoC fext u2 -> u1 = u2
    IRtoCinj fext (InIRC (Left i1)) (InIRC (Left i2)) eq =
      cong IRCiota (iotaCodeInj i1 i2 eq)
    IRtoCinj fext (InIRC (Left _)) (InIRC (Right (Left (_ ** _)))) eq =
      absurd (the (True = False) (cong isIotaC eq))
    IRtoCinj fext (InIRC (Left _)) (InIRC (Right (Right (_ ** _)))) eq =
      absurd (the (True = False) (cong isIotaC eq))
    IRtoCinj fext (InIRC (Right (Left (_ ** _)))) (InIRC (Left _)) eq =
      absurd (the (False = True) (cong isIotaC eq))
    IRtoCinj fext (InIRC (Right (Right (_ ** _)))) (InIRC (Left _)) eq =
      absurd (the (False = True) (cong isIotaC eq))
    IRtoCinj fext
      (InIRC (Right (Left (_ ** _)))) (InIRC (Right (Right (_ ** _)))) eq =
      absurd (the (True = False) (cong isSigmaC eq))
    IRtoCinj fext
      (InIRC (Right (Right (_ ** _)))) (InIRC (Right (Left (_ ** _)))) eq =
      absurd (the (False = True) (cong isSigmaC eq))
    IRtoCinj fext (InIRC (Right (Left (u1 ** f1))))
        (InIRC (Right (Left (u2 ** f2)))) eq =
      IRCsigmaCong fext u1 f1 u2 f2
        (IRsigmaInjBase fext u1 f1 u2 f2 eq)
        (IRsigmaInjStep fext u1 f1 u2 f2 eq)
    IRtoCinj fext (InIRC (Right (Right (u1 ** f1))))
        (InIRC (Right (Right (u2 ** f2)))) eq =
      IRCpiCong fext u1 f1 u2 f2
        (IRpiInjBase fext u1 f1 u2 f2 eq)
        (IRpiInjStep fext u1 f1 u2 f2 eq)

    public export
    partial
    IRsigmaInjBase : (fext : FunExt) ->
      (u1 : IRCode) -> (f1 : IRdecode u1 -> IRCode) ->
      (u2 : IRCode) -> (f2 : IRdecode u2 -> IRCode) ->
      IRtoC fext (IRCsigma u1 f1) = IRtoC fext (IRCsigma u2 f2) -> u1 = u2
    IRsigmaInjBase fext u1 f1 u2 f2 eq =
      IRtoCinj fext u1 u2
        (sigmaCodeInjFst
          (IRtoC fext u1) (\w => IRtoC fext (f1 (tiFrom (IRdecIso fext u1) w)))
          (IRtoC fext u2) (\w => IRtoC fext (f2 (tiFrom (IRdecIso fext u2) w)))
          eq)

    public export
    partial
    IRsigmaInjStep : (fext : FunExt) ->
      (u1 : IRCode) -> (f1 : IRdecode u1 -> IRCode) ->
      (u2 : IRCode) -> (f2 : IRdecode u2 -> IRCode) ->
      (eq : IRtoC fext (IRCsigma u1 f1) = IRtoC fext (IRCsigma u2 f2)) ->
      (d : IRdecode u1) ->
      f1 d =
        f2 (replace {p=IRdecode} {x=u1} {y=u2}
              (IRsigmaInjBase fext u1 f1 u2 f2 eq) d)
    IRsigmaInjStep fext u1 f1 u2 f2 eq d =
      IRtoCinj fext (f1 d)
        (f2 (replace {p=IRdecode} {x=u1} {y=u2}
              (IRsigmaInjBase fext u1 f1 u2 f2 eq) d)) $
        trans
          (sym
            (cong (\y => IRtoC fext (f1 y)) (tiFromTo (IRdecIso fext u1) d)))
          (trans
            (sigmaCodeInjSnd
              (IRtoC fext u1)
              (\w => IRtoC fext (f1 (tiFrom (IRdecIso fext u1) w)))
              (IRtoC fext u2)
              (\w => IRtoC fext (f2 (tiFrom (IRdecIso fext u2) w)))
              eq (tiTo (IRdecIso fext u1) d))
            (cong (\y => IRtoC fext (f2 y))
              (IRdecIsoCoh fext u1 u2
                (IRsigmaInjBase fext u1 f1 u2 f2 eq)
                (sigmaCodeInjFst
                  (IRtoC fext u1)
                  (\w => IRtoC fext (f1 (tiFrom (IRdecIso fext u1) w)))
                  (IRtoC fext u2)
                  (\w => IRtoC fext (f2 (tiFrom (IRdecIso fext u2) w)))
                  eq)
                d)))

    public export
    partial
    IRpiInjBase : (fext : FunExt) ->
      (u1 : IRCode) -> (f1 : IRdecode u1 -> IRCode) ->
      (u2 : IRCode) -> (f2 : IRdecode u2 -> IRCode) ->
      IRtoC fext (IRCpi u1 f1) = IRtoC fext (IRCpi u2 f2) -> u1 = u2
    IRpiInjBase fext u1 f1 u2 f2 eq =
      IRtoCinj fext u1 u2
        (piCodeInjFst
          (IRtoC fext u1) (\w => IRtoC fext (f1 (tiFrom (IRdecIso fext u1) w)))
          (IRtoC fext u2) (\w => IRtoC fext (f2 (tiFrom (IRdecIso fext u2) w)))
          eq)

    public export
    partial
    IRpiInjStep : (fext : FunExt) ->
      (u1 : IRCode) -> (f1 : IRdecode u1 -> IRCode) ->
      (u2 : IRCode) -> (f2 : IRdecode u2 -> IRCode) ->
      (eq : IRtoC fext (IRCpi u1 f1) = IRtoC fext (IRCpi u2 f2)) ->
      (d : IRdecode u1) ->
      f1 d =
        f2 (replace {p=IRdecode} {x=u1} {y=u2}
              (IRpiInjBase fext u1 f1 u2 f2 eq) d)
    IRpiInjStep fext u1 f1 u2 f2 eq d =
      IRtoCinj fext (f1 d)
        (f2 (replace {p=IRdecode} {x=u1} {y=u2}
              (IRpiInjBase fext u1 f1 u2 f2 eq) d)) $
        trans
          (sym
            (cong (\y => IRtoC fext (f1 y)) (tiFromTo (IRdecIso fext u1) d)))
          (trans
            (piCodeInjSnd
              (IRtoC fext u1)
              (\w => IRtoC fext (f1 (tiFrom (IRdecIso fext u1) w)))
              (IRtoC fext u2)
              (\w => IRtoC fext (f2 (tiFrom (IRdecIso fext u2) w)))
              eq (tiTo (IRdecIso fext u1) d))
            (cong (\y => IRtoC fext (f2 y))
              (IRdecIsoCoh fext u1 u2
                (IRpiInjBase fext u1 f1 u2 f2 eq)
                (piCodeInjFst
                  (IRtoC fext u1)
                  (\w => IRtoC fext (f1 (tiFrom (IRdecIso fext u1) w)))
                  (IRtoC fext u2)
                  (\w => IRtoC fext (f2 (tiFrom (IRdecIso fext u2) w)))
                  eq)
                d)))


  -------------------------------------------------
  -------------------------------------------------
  ---- The equivalence of the two formulations ----
  -------------------------------------------------
  -------------------------------------------------

  -- The codes are isomorphic ...
  public export
  partial
  IRcodeIso : (fext : FunExt) -> TIso IRCode IRCode'
  IRcodeIso fext =
    MkTIso (IRtoC fext) (IRcodeInv fext)
      (\u =>
        IRtoCinj fext (IRcodeInv fext (IRtoC fext u)) u
          (IRcodeInvEq fext (IRtoC fext u)))
      (IRcodeInvEq fext)

  -- ... and over corresponding codes, the inductive-recursive decoding
  -- is the fibre of the inductive-inductive `IRfib`.
  public export
  partial
  IRdecFibIso : (fext : FunExt) -> (u : IRCode) ->
    TIso (IRdecode u) (IRFib (tiTo (IRcodeIso fext) u))
  IRdecFibIso = IRdecIso

--------------------------------------------------
--------------------------------------------------
---- The natural numbers as the original case ----
--------------------------------------------------
--------------------------------------------------

-- The formulation before the generalization is `idx = Unit` with a
-- single starting type `Nat`.
public export
IRnatIdx : Type
IRnatIdx = Unit

public export
IRnatSty : IRnatIdx -> Type
IRnatSty () = Nat

-- A compile-time check that the specialization decodes as it did:
-- the dependent sum of two copies of the starting type is a pair of
-- natural numbers.
public export
IRnatPair : IRCode IRnatIdx IRnatSty
IRnatPair =
  IRCsigma IRnatIdx IRnatSty
    (IRCiota IRnatIdx IRnatSty ())
    (\_ => IRCiota IRnatIdx IRnatSty ())

public export
IRnatPairDecodes : IRdecode IRnatIdx IRnatSty IRnatPair = (x : Nat ** Nat)
IRnatPairDecodes = Refl

---------------------------------------------
---------------------------------------------
---- Codes for small induction-recursion ----
---------------------------------------------
---------------------------------------------

-- Definition 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013].  A
-- code describes an inductive-recursive definition whose recursive
-- calls return elements of `i` and which itself decodes into `o`:
--
--   `SIRiota t`      -- stop, decoding to `t`
--   `SIRsigma s k`   -- a non-recursive field of type `s`, then `k`
--   `SIRdelta p k`   -- a `p`-indexed family of recursive fields;
--                       `k` receives their *decoded values*
--
-- The paper writes these as `iota`, `sigma` and `delta`.  The whole
-- point of `SIRdelta` is that its continuation sees the decodings, so
-- later fields' types may depend on earlier fields' values.
public export
data SmallIR : (i, o : Type) -> Type where
  SIRiota : {0 i, o : Type} -> o -> SmallIR i o
  SIRsigma : {0 i, o : Type} ->
    (s : Type) -> (s -> SmallIR i o) -> SmallIR i o
  SIRdelta : {0 i, o : Type} ->
    (p : Type) -> ((p -> i) -> SmallIR i o) -> SmallIR i o

-- An object of the slice `Set/i`:  a type with a map to `i`.  The
-- base category of the universe example is the case `i = Type`, where
-- a map to `Type` is a family -- hence `IRFam`.
public export
IRSlice : Type -> Type
IRSlice i = (ty : Type ** ty -> i)

public export
irFamIsSlice : (0 a : Type) -> (0 b : a -> Type) -> IRFam a b = IRSlice Type
irFamIsSlice a b = Refl


---------------------------------------
---------------------------------------
---- The functor denoted by a code ----
---------------------------------------
---------------------------------------

-- The interpretation of a code as a functor `Set/i -> Set/o`, broken
-- into its two components exactly as `IRUnivPos`/`IRUnivDec` were.
-- This is the paper's `[[.]]_DS`.

-- The shapes:  what one node of the described data type contains.
public export
SmallIRPos : {0 i, o : Type} -> SmallIR i o -> IRSlice i -> Type
SmallIRPos (SIRiota _) x = Unit
SmallIRPos (SIRsigma s k) x = (e : s ** SmallIRPos (k e) x)
SmallIRPos (SIRdelta p k) x = (g : p -> fst x ** SmallIRPos (k (snd x . g)) x)

-- The decoding of each shape.  In the `SIRdelta` case `snd x . g` is
-- the tuple of decoded values of the recursive fields, which is what
-- the continuation `k` was given.
public export
SmallIRDec : {0 i, o : Type} -> (c : SmallIR i o) -> (x : IRSlice i) ->
  SmallIRPos c x -> o
SmallIRDec (SIRiota t) x () = t
SmallIRDec (SIRsigma s k) x (e ** r) = SmallIRDec (k e) x r
SmallIRDec (SIRdelta p k) x (g ** r) = SmallIRDec (k (snd x . g)) x r

public export
SmallIRF : {0 i, o : Type} -> SmallIR i o -> IRSlice i -> IRSlice o
SmallIRF c x = (SmallIRPos c x ** SmallIRDec c x)

-----------------------------------------------------
-----------------------------------------------------
---- Small IR codes as slice polynomial functors ----
-----------------------------------------------------
-----------------------------------------------------

-- Lemma 2 / Definition 5 of
-- [HancockMcBrideGhaniMalatestaAltenkirch2013], following
-- `IR.toSlicePFunctor` in the Lean
-- `Geb.Mathlib.Data.PFunctor.IndRec.Slice`.  A `SmallIR i o` code
-- denotes a functor `Set/i -> Set/o`, and `SPFData i o` is a code for
-- exactly such a functor, with `InterpSPFData` its interpretation.
--
-- The shapes of an `SPFData` are already fibred over the output
-- index, so where the Lean carries a global shape set `A` with a map
-- `q : A -> O`, here `spfdPos ec` is directly the fibre over `ec`.

-- `InterpSPFData` is built as a composite, but it computes to the
-- expected "a shape, and a choice of element for each direction".
public export
interpSPFDataPair : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x : SliceObj dom) -> (ec : cod) ->
  InterpSPFData spfd x ec =
    (ep : spfdPos spfd ec ** SliceMorphism {a=dom} (spfdDir spfd ec ep) x)
interpSPFDataPair spfd x ec = Refl

-- `SIRiota t` has one shape, over the output index `t` alone, and no
-- directions.
public export
smallIRtoSPFiota : {i, o : Type} -> o -> SPFData i o
smallIRtoSPFiota {i} {o} t = SPFD (\ec => t = ec) (\_, _, _ => Void)

-- `SIRsigma s k` is the coproduct, over the arity, of the subcodes'
-- functors.
public export
smallIRtoSPFsigma : {i, o : Type} -> (s : Type) -> (s -> SPFData i o) ->
  SPFData i o
smallIRtoSPFsigma {i} {o} s sub = spfdSetCoproduct {b=s} {dom=i} {cod=o} sub

-- `SIRdelta p k` is the coproduct, over the assignments `assign : p ->
-- i` of input indices to the recursive fields, of the product of the
-- subcode's functor at `assign` with the functor `assign` represents.
-- That representable has a single shape, so the product's shapes are
-- just the subcode's, and its directions are the subcode's together
-- with the `p` recursive fields -- whence the `Either`.  (The Lean
-- notes the same point:  its summand's shapes are `PUnit x (sub i).A`
-- rather than `(sub i).A`, and the two are isomorphic.  Taking the
-- product by hand here avoids that isomorphism.)
public export
smallIRtoSPFdelta : {i, o : Type} -> (p : Type) ->
  ((p -> i) -> SPFData i o) -> SPFData i o
smallIRtoSPFdelta {i} {o} p sub =
  spfdSetCoproduct {b=(p -> i)} {dom=i} {cod=o} (\assign =>
    SPFD
      (spfdPos (sub assign))
      (\ec, ep, ed =>
        Either (q : p ** assign q = ed) (spfdDir (sub assign) ec ep ed)))

public export
smallIRtoSPFData : {i, o : Type} -> SmallIR i o -> SPFData i o
smallIRtoSPFData (SIRiota t) = smallIRtoSPFiota t
smallIRtoSPFData (SIRsigma s k) =
  smallIRtoSPFsigma s (\a => smallIRtoSPFData (k a))
smallIRtoSPFData (SIRdelta p k) =
  smallIRtoSPFdelta p (\assign => smallIRtoSPFData (k assign))


-----------------------------------------------------
-----------------------------------------------------
---- Slice polynomial functors as small IR codes ----
-----------------------------------------------------
-----------------------------------------------------

-- Lemma 1, following `IR.sliceCode` in the Lean.  Choose a shape,
-- take a recursive field for each of its directions, check that the
-- fields landed at the input indices the directions call for, and
-- stop at the shape's output index.
--
-- The global shape set of an `SPFData` is `Sigma cod spfdPos`, and
-- the global direction set of a shape is `Sigma dom (spfdDir ...)`,
-- whose first component is the direction's input index -- which is
-- what the `SIRsigma` constraint compares the assignment against.
-- As in `smallIIRtoIR`, that equality is stated pointwise.
public export
spfDataToSmallIR : {dom, cod : Type} -> SPFData dom cod -> SmallIR dom cod
spfDataToSmallIR {dom} {cod} spfd =
  SIRsigma (ec : cod ** spfdPos spfd ec) (\a =>
    SIRdelta (ed : dom ** spfdDir spfd (fst a) (snd a) ed) (\assign =>
      SIRsigma
        ((q : (ed : dom ** spfdDir spfd (fst a) (snd a) ed)) ->
           assign q = fst q)
        (\_ => SIRiota (fst a))))


------------------------------------------------------
------------------------------------------------------
---- The translation preserves the interpretation ----
------------------------------------------------------
------------------------------------------------------

-- One half of Lemma 2:  a node of the functor a code denotes is a
-- node of the functor its translation denotes, at the same output
-- index.  An `IRSlice i` whose decoding is a first projection is the
-- same thing as a `SliceObj i`, so the statement is over the latter.
--
-- This is what lets a fixed point of the *translated* code stand in
-- for a fixed point of the code itself.
public export
smallIRPosToSPF : {i, o : Type} -> (c : SmallIR i o) -> (x : SliceObj i) ->
  (z : SmallIRPos c (Sigma {a=i} x ** DPair.fst)) ->
  InterpSPFData (smallIRtoSPFData c) x
    (SmallIRDec c (Sigma {a=i} x ** DPair.fst) z)
smallIRPosToSPF (SIRiota t) x () = (Refl ** \_, v => void v)
smallIRPosToSPF (SIRsigma s k) x (a ** z) =
  InterpSPFnt
    (smallIRtoSPFData (k a))
    (smallIRtoSPFsigma s (\a' => smallIRtoSPFData (k a')))
    (spfdSetCoproductInj (\a' => smallIRtoSPFData (k a')) a)
    x
    (SmallIRDec (k a) (Sigma {a=i} x ** DPair.fst) z)
    (smallIRPosToSPF (k a) x z)
smallIRPosToSPF (SIRdelta p k) x (g ** z) =
  InterpSPFnt
    (SPFD
      (spfdPos (smallIRtoSPFData (k (\q => fst (g q)))))
      (\ec, ep, ed =>
        Either (q : p ** fst (g q) = ed)
          (spfdDir (smallIRtoSPFData (k (\q => fst (g q)))) ec ep ed)))
    (smallIRtoSPFdelta p (\assign => smallIRtoSPFData (k assign)))
    (spfdSetCoproductInj
      (\assign =>
        SPFD
          (spfdPos (smallIRtoSPFData (k assign)))
          (\ec, ep, ed =>
            Either (q : p ** assign q = ed)
              (spfdDir (smallIRtoSPFData (k assign)) ec ep ed)))
      (\q => fst (g q)))
    x
    (SmallIRDec (k (\q => fst (g q))) (Sigma {a=i} x ** DPair.fst) z)
    (fst (smallIRPosToSPF (k (\q => fst (g q))) x z) **
     \ed, e => case e of
       Left (q ** eq) => replace {p=x} eq (snd (g q))
       Right dq => snd (smallIRPosToSPF (k (\q => fst (g q))) x z) ed dq)


-- The initial algebra of `SmallIRF c` for an endo-code `c`, giving
-- the data type and its decoder simultaneously.
--
-- Defining this directly needs `partial`:  `SmallIRPos c X` cannot
-- reduce while `c` is a variable, so the positivity checker rejects
-- the fixed point.  Going through the translation avoids that
-- entirely.  `SPFDmu` is an ordinary, total, strictly positive
-- inductive family, so the fixed point of the *translated* code is
-- total; taking its total space and reading the decoding off as the
-- first projection recovers the pair `(mu, decode)` -- the `Set/i`
-- object the fixed point is meant to be.
public export
SmallIRMu : {i : Type} -> SmallIR i i -> Type
SmallIRMu {i} c = Sigma {a=i} (SPFDmu {x=i} (smallIRtoSPFData c))

public export
SmallIRDecode : {i : Type} -> (c : SmallIR i i) -> SmallIRMu c -> i
SmallIRDecode c = DPair.fst

-- The algebra map, in place of the former data constructor:  a node
-- whose recursive fields are already elements decodes to some index,
-- and `smallIRPosToSPF` presents that node as a node of the
-- translated functor at exactly that index, where `InSPFm` accepts
-- it.  `SmallIRDecode c (InSIR z) = SmallIRDec c _ z` then holds by
-- construction, since the decoding is the first projection.
public export
InSIR : {i : Type} -> {c : SmallIR i i} ->
  SmallIRPos c (SmallIRMu c ** SmallIRDecode c) -> SmallIRMu c
InSIR {i} {c} z =
  (SmallIRDec c (SmallIRMu c ** SmallIRDecode c) z **
   InSPFm {x=i} {spfd=(smallIRtoSPFData c)}
     (SmallIRDec c (SmallIRMu c ** SmallIRDecode c) z)
     (smallIRPosToSPF c (SPFDmu {x=i} (smallIRtoSPFData c)) z))


-----------------------------------------------------
-----------------------------------------------------
---- Example 2:  a language of sums and products ----
-----------------------------------------------------
-----------------------------------------------------

-- Finitary summation and product, the paper's `sum` and `prod`.
public export
sumFin : (n : Nat) -> (Fin n -> Nat) -> Nat
sumFin Z f = 0
sumFin (S n) f = f FZ + sumFin n (f . FS)

public export
prodFin : (n : Nat) -> (Fin n -> Nat) -> Nat
prodFin Z f = 1
prodFin (S n) f = f FZ * prodFin n (f . FS)

-- Numerical expressions closed under constants, finite sums and
-- finite products, where each expression decodes to its value.  The
-- values are needed to state the *types* of the sub-expressions:  a
-- sum ranges over `Fin` of the value of its bound, so the data and
-- the decoding must be defined together.
public export
data LangTag : Type where
  LTfin : LangTag
  LTsum : LangTag
  LTprod : LangTag

public export
langK : LangTag -> SmallIR Nat Nat
langK LTfin =
  SIRsigma Nat (\n => SIRiota n)
langK LTsum =
  SIRdelta Unit (\n =>
    SIRdelta (Fin (n ())) (\f => SIRiota (sumFin (n ()) f)))
langK LTprod =
  SIRdelta Unit (\n =>
    SIRdelta (Fin (n ())) (\f => SIRiota (prodFin (n ()) f)))

public export
lang : SmallIR Nat Nat
lang = SIRsigma LangTag langK


----------------------------------
----------------------------------
---- What the code unfolds to ----
----------------------------------
----------------------------------

-- The paper's code read back out in ordinary type-theoretic language.
-- Each of these holds by `Refl`:  they are not a separate definition
-- of the language but a machine-checked reading of `lang`.

-- A constant node carries a literal, and decodes to it.
public export
langFinNode : (x : IRSlice Nat) ->
  SmallIRPos (langK LTfin) x = (n : Nat ** Unit)
langFinNode x = Refl

public export
langFinValue : (x : IRSlice Nat) -> (n : Nat) ->
  SmallIRDec (langK LTfin) x (n ** ()) = n
langFinValue x n = Refl

-- A sum node carries one recursive sub-expression `g` -- the bound --
-- and then a family of sub-expressions indexed by `Fin` of the
-- bound's *value*.  `SIRdelta Unit` is the paper's `delta 1`:  a
-- single recursive field, presented as a function from `Unit`.
public export
langSumNode : (x : IRSlice Nat) ->
  SmallIRPos (langK LTsum) x =
    (g : Unit -> fst x ** (h : Fin (snd x (g ())) -> fst x ** Unit))
langSumNode x = Refl

public export
langSumValue : (x : IRSlice Nat) -> (g : Unit -> fst x) ->
  (h : Fin (snd x (g ())) -> fst x) ->
  SmallIRDec (langK LTsum) x (g ** (h ** ())) =
    sumFin (snd x (g ())) (snd x . h)
langSumValue x g h = Refl

public export
langProdNode : (x : IRSlice Nat) ->
  SmallIRPos (langK LTprod) x =
    (g : Unit -> fst x ** (h : Fin (snd x (g ())) -> fst x ** Unit))
langProdNode x = Refl

public export
langProdValue : (x : IRSlice Nat) -> (g : Unit -> fst x) ->
  (h : Fin (snd x (g ())) -> fst x) ->
  SmallIRDec (langK LTprod) x (g ** (h ** ())) =
    prodFin (snd x (g ())) (snd x . h)
langProdValue x g h = Refl


-----------------------------------------------
-----------------------------------------------
---- The language, and the paper's example ----
-----------------------------------------------
-----------------------------------------------

public export
Lang : Type
Lang = SmallIRMu lang

public export
langValue : Lang -> Nat
langValue = SmallIRDecode lang

public export
LFin : Nat -> Lang
LFin n = InSIR {c=lang} (LTfin ** (n ** ()))

-- Note how the type of the summand family depends on `langValue b`:
-- the bound's value, not the bound.
public export
LSum : (b : Lang) -> (Fin (langValue b) -> Lang) -> Lang
LSum b h = InSIR {c=lang} (LTsum ** ((\_ => b) ** (h ** ())))

public export
LProd : (b : Lang) -> (Fin (langValue b) -> Lang) -> Lang
LProd b h = InSIR {c=lang} (LTprod ** ((\_ => b) ** (h ** ())))

-- `sum (n < 5) n`.  The paper writes the summand as `\ n -> in
-- (fin', n, *)`, silently coercing `n : Fin 5` to a natural number;
-- `finToNat` is that coercion made explicit.
public export
LangExample : Lang
LangExample = LSum (LFin 5) (\n => LFin (finToNat n))

-- The paper states this example decodes to 10, and it does.
public export
LangExampleValue : langValue LangExample = 10
LangExampleValue = Refl

-----------------------------------------------------
-----------------------------------------------------
---- Codes for small indexed induction-recursion ----
-----------------------------------------------------
-----------------------------------------------------

-- Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013].  Where a
-- `SmallIR` code describes one inductive-recursive definition, a
-- `SmallIIR` code describes a whole *family* of them, indexed by `i`
-- on the way in and by `j` on the way out, with `d` and `e` giving
-- the type each decodes into at each index.
--
-- Two things change from `SmallIR`:  `SIIRiota` now names the output
-- index it lands at, as well as the value it decodes to; and
-- `SIIRdelta` carries an extra `ix`, choosing the input index of each
-- recursive field.  Ordinary `SmallIR` is the case where `i` and `j`
-- are singletons.
public export
data SmallIIR : (i : Type) -> (i -> Type) -> (j : Type) -> (j -> Type) ->
    Type where
  SIIRiota : {0 i : Type} -> {0 d : i -> Type} ->
    {0 j : Type} -> {0 e : j -> Type} ->
    (je : (m : j ** e m)) -> SmallIIR i d j e
  SIIRsigma : {0 i : Type} -> {0 d : i -> Type} ->
    {0 j : Type} -> {0 e : j -> Type} ->
    (s : Type) -> (s -> SmallIIR i d j e) -> SmallIIR i d j e
  SIIRdelta : {0 i : Type} -> {0 d : i -> Type} ->
    {0 j : Type} -> {0 e : j -> Type} ->
    (p : Type) -> (ix : p -> i) ->
    (((q : p) -> d (ix q)) -> SmallIIR i d j e) -> SmallIIR i d j e

-- The paper's `delta_1`:  a single recursive field at index `n`,
-- presented as a `Unit`-indexed family.  Its continuation receives
-- that field's decoded value, which is what lets the *shape* of the
-- rest of the node depend on it.
public export
siirDelta1 : {0 i : Type} -> {0 d : i -> Type} ->
  {0 j : Type} -> {0 e : j -> Type} ->
  (n : i) -> (d n -> SmallIIR i d j e) -> SmallIIR i d j e
siirDelta1 n k = SIIRdelta Unit (\_ => n) (\dv => k (dv ()))


------------------------------------------------------
------------------------------------------------------
---- The base category:  slices over a sigma type ----
------------------------------------------------------
------------------------------------------------------

-- An object is a slice over `d n` for each index `n`.
public export
IIRSlice : (i : Type) -> (i -> Type) -> Type
IIRSlice i d = (n : i) -> IRSlice (d n)

-- Read fibrewise instead, that is a family over `i` and then over
-- `d n` -- which is exactly a slice over the total space `Sigma i d`,
-- up to currying.  This is the sense in which indexed
-- induction-recursion is about functors between slices over sigma
-- types.
public export
IIRFam : (i : Type) -> (i -> Type) -> Type
IIRFam i d = (n : i) -> d n -> Type

public export
iirFamSigmaIso : FunExt -> (i : Type) -> (d : i -> Type) ->
  TIso (IIRFam i d) (SliceObj (n : i ** d n))
iirFamSigmaIso fext i d =
  MkTIso
    (\f, x => f (fst x) (snd x))
    (\g, n, dv => g (n ** dv))
    (\_ => Refl)
    (\g => funExt $ \x => cong g (sym $ dpEqPat {dp=x}))


------------------------------------------------
------------------------------------------------
---- The functor denoted by an indexed code ----
------------------------------------------------
------------------------------------------------

-- The shapes, at each output index.  `SIIRiota` contributes only the
-- proof that it landed at the index asked for.
public export
SmallIIRPos : {0 i : Type} -> {0 d : i -> Type} ->
  {0 j : Type} -> {0 e : j -> Type} ->
  SmallIIR i d j e -> IIRSlice i d -> j -> Type
SmallIIRPos (SIIRiota (m ** _)) g n = m = n
SmallIIRPos (SIIRsigma s k) g n = (a : s ** SmallIIRPos (k a) g n)
SmallIIRPos (SIIRdelta p ix k) g n =
  (ig : (q : p) -> fst (g (ix q)) **
   SmallIIRPos (k (\q => snd (g (ix q)) (ig q))) g n)

-- The decoding.  Transporting the `SIIRiota` value along its index
-- proof is the paper's `\ q -> . q e`.
public export
SmallIIRDec : {0 i : Type} -> {0 d : i -> Type} ->
  {0 j : Type} -> {0 e : j -> Type} ->
  (c : SmallIIR i d j e) -> (g : IIRSlice i d) -> (n : j) ->
  SmallIIRPos c g n -> e n
SmallIIRDec (SIIRiota (m ** ev)) g n q = replace {p=e} q ev
SmallIIRDec (SIIRsigma s k) g n (a ** r) = SmallIIRDec (k a) g n r
SmallIIRDec (SIIRdelta p ix k) g n (ig ** r) =
  SmallIIRDec (k (\q => snd (g (ix q)) (ig q))) g n r

public export
SmallIIRF : {0 i : Type} -> {0 d : i -> Type} ->
  {0 j : Type} -> {0 e : j -> Type} ->
  SmallIIR i d j e -> IIRSlice i d -> IIRSlice j e
SmallIIRF c g n = (SmallIIRPos c g n ** SmallIIRDec c g n)

--------------------------------------------------------
--------------------------------------------------------
---- Reducing indexed induction-recursion to plain IR ----
--------------------------------------------------------
--------------------------------------------------------

-- The paper's `|_|` (Section 6):  an indexed code over `i`/`j` with
-- decodings `d`/`e` becomes a plain code over the total spaces
-- `Sigma i d` and `Sigma j e`.
--
-- `SIIRiota` and `SIIRsigma` carry across unchanged.  The work is in
-- `SIIRdelta`:  a recursive field of the plain code decodes to a
-- *pair* of an index and a value, so the translation cannot ask for a
-- field at a chosen index directly.  Instead it takes the fields
-- wherever they land and then adds a `SIRsigma` whose field is the
-- proof that they landed at the indices `ix` demanded -- the paper's
-- `sigma (i = pi_0 . iD)`.  Those proofs are then what lets the
-- values be transported into the types the continuation expects.
--
-- The equality is stated pointwise rather than between the two index
-- functions, so that building one needs no functional extensionality.
public export
smallIIRtoIR : {0 i : Type} -> {0 d : i -> Type} ->
  {0 j : Type} -> {0 e : j -> Type} ->
  SmallIIR i d j e -> SmallIR (n : i ** d n) (m : j ** e m)
smallIIRtoIR (SIIRiota je) = SIRiota je
smallIIRtoIR (SIIRsigma s k) = SIRsigma s (\a => smallIIRtoIR (k a))
smallIIRtoIR (SIIRdelta p ix k) =
  SIRdelta p (\iD =>
    SIRsigma ((q : p) -> fst (iD q) = ix q) (\cq =>
      smallIIRtoIR (k (\q => replace {p=d} (cq q) (snd (iD q))))))

-- The fixed point of an indexed code is now *derived*:  take the
-- fixed point of the translated plain code, whose decoding lands in
-- `Sigma i d`, and cut it into fibres over the index.  This is the
-- paper's remark that the corresponding fixpoint gives the inductive
-- family indexed by pairs in `Sigma D`.
public export
SmallIIRMu : {i : Type} -> {d : i -> Type} ->
  SmallIIR i d i d -> i -> Type
SmallIIRMu c n =
  (x : SmallIRMu (smallIIRtoIR c) **
   DPair.fst (SmallIRDecode (smallIIRtoIR c) x) = n)

-- ... and the decoder is the second component of that decoding,
-- transported along the fibre's index proof.
public export
SmallIIRDecode : {i : Type} -> {d : i -> Type} ->
  (c : SmallIIR i d i d) -> (n : i) -> SmallIIRMu c n -> d n
SmallIIRDecode c n x =
  replace {p=d} (DPair.snd x)
    (DPair.snd (SmallIRDecode (smallIIRtoIR c) (DPair.fst x)))


-------------------------------------------------------------
-------------------------------------------------------------
---- Example 3:  lambda terms and de Bruijn substitution ----
-------------------------------------------------------------
-------------------------------------------------------------

public export
data Tm : Type where
  TVar : Nat -> Tm
  TApp : Tm -> Tm -> Tm
  TLam : Tm -> Tm

-- Raise the free variables at or above `c` by one.
public export
tmShift : Nat -> Tm -> Tm
tmShift c (TVar k) = if k < c then TVar k else TVar (S k)
tmShift c (TApp f s) = TApp (tmShift c f) (tmShift c s)
tmShift c (TLam t) = TLam (tmShift (S c) t)

-- Substitute `s` for the variable `n`, decrementing the free
-- variables above it, since the binder `n` is being removed.
public export
tmSubst : Nat -> Tm -> Tm -> Tm
tmSubst n s (TVar k) =
  case compare k n of
    LT => TVar k
    EQ => s
    GT => TVar (pred k)
tmSubst n s (TApp f t) = TApp (tmSubst n s f) (tmSubst n s t)
tmSubst n s (TLam t) = TLam (tmSubst (S n) (tmShift 0 s) t)

public export
subst0 : Tm -> Tm -> Tm
subst0 s t = tmSubst 0 s t


-----------------------------------------------------------------
-----------------------------------------------------------------
---- Example 3:  the Bove-Capretta domain of a cbv evaluator ----
-----------------------------------------------------------------
-----------------------------------------------------------------

-- The call-by-value evaluator we would like to write is
--
--   cbv (var x) = var x
--   cbv (lam t) = lam t
--   cbv (app f s) with cbv f
--     | lam t = cbv (subst0 (cbv s) t)
--     | f'    = app f' (cbv s)
--
-- which is not structurally recursive:  in the `app` case the third
-- recursive call is made at `subst0 (cbv s) t`, a term built from the
-- *results* of the first two.  The Bove-Capretta method makes the
-- domain of such a function an inductive family; because the domain
-- here mentions the results, it must be defined simultaneously with
-- the evaluation -- a job for induction-recursion.
--
-- Both indices are `Tm` and both decodings are the constant family
-- `\ _ => Tm`:  the index is the term being evaluated, and the
-- decoded value is the term it evaluates to.
public export
CbvBranchTy : Type
CbvBranchTy = SmallIIR Tm (\_ => Tm) Tm (\_ => Tm)

-- The `app` case, once the function part's value `fv` is known.  This
-- is the branch the paper writes as a `with`:  the code taken depends
-- on a value delivered by an earlier recursive field.
public export
cbvApp : (f, s : Tm) -> Tm -> CbvBranchTy
cbvApp f s (TLam t) =
  siirDelta1 s (\sv =>
    siirDelta1 (subst0 sv t) (\tv => SIIRiota (TApp f s ** tv)))
cbvApp f s fv =
  siirDelta1 s (\sv => SIIRiota (TApp f s ** TApp fv sv))

public export
cbvBranch : Tm -> CbvBranchTy
cbvBranch (TVar x) = SIIRiota (TVar x ** TVar x)
cbvBranch (TLam t) = SIIRiota (TLam t ** TLam t)
cbvBranch (TApp f s) = siirDelta1 f (cbvApp f s)

public export
CbvD : CbvBranchTy
CbvD = SIIRsigma Tm cbvBranch

-- `CbvDom t` is the evidence that the evaluator terminates on `t`,
-- and `cbvEval t` reads the resulting value off that evidence.
public export
CbvDom : Tm -> Type
CbvDom = SmallIIRMu CbvD

public export
cbvEval : (t : Tm) -> CbvDom t -> Tm
cbvEval = SmallIIRDecode CbvD


------------------------------------------
------------------------------------------
---- What the indexed code unfolds to ----
------------------------------------------
------------------------------------------

-- As with `lang`, these hold by `Refl` and so are a checked reading
-- of the code rather than a second definition of it.

-- A value -- a variable or a lambda -- needs no recursive evidence,
-- only the proof that it is the term being evaluated.
public export
cbvLamNode : (g : IIRSlice Tm (\_ => Tm)) -> (t, n : Tm) ->
  SmallIIRPos (cbvBranch (TLam t)) g n = (TLam t = n)
cbvLamNode g t n = Refl

-- An application node holds evidence for the function part, and then
-- evidence whose *shape* is chosen by that part's value.
public export
cbvAppNode : (g : IIRSlice Tm (\_ => Tm)) -> (f, s, n : Tm) ->
  SmallIIRPos (cbvBranch (TApp f s)) g n =
    (ig : Unit -> fst (g f) **
     SmallIIRPos (cbvApp f s (snd (g f) (ig ()))) g n)
cbvAppNode g f s n = Refl

-- When the function part evaluates to a lambda, the node continues
-- with evidence for the argument and then for the substituted body,
-- at an index built from the argument's value.
public export
cbvBetaNode : (g : IIRSlice Tm (\_ => Tm)) -> (f, s, t, n : Tm) ->
  SmallIIRPos (cbvApp f s (TLam t)) g n =
    (jg : Unit -> fst (g s) **
     (kg : Unit -> fst (g (subst0 (snd (g s) (jg ())) t)) **
      TApp f s = n))
cbvBetaNode g f s t n = Refl


---------------------------------------------------------------
---------------------------------------------------------------
---- Example 3:  evaluating the identity applied to itself ----
---------------------------------------------------------------
---------------------------------------------------------------

public export
CbvId : Tm
CbvId = TLam (TVar 0)

-- Evidence now lives in the *translated* plain code, so it is built
-- with `InSIR`.  A value -- here a lambda -- reaches a `SIRiota`
-- immediately, whose shape is `Unit`.
public export
cbvValueMu : (t : Tm) -> SmallIRMu (smallIIRtoIR CbvD)
cbvValueMu t = InSIR {c=(smallIIRtoIR CbvD)} (TLam t ** ())

public export
cbvValueEvidence : (t : Tm) -> CbvDom (TLam t)
cbvValueEvidence t = (cbvValueMu t ** Refl)

public export
cbvIdMu : Unit -> SmallIRMu (smallIIRtoIR CbvD)
cbvIdMu _ = cbvValueMu (TVar 0)

public export
CbvIdApp : Tm
CbvIdApp = TApp CbvId CbvId

-- Evidence that the evaluator terminates on `(\x. x) (\x. x)`:  one
-- recursive field for the function part, one for the argument, and
-- one for the substituted body, which here is the identity again.
--
-- The translation shows up as the `\ _ => Refl` beside each field:
-- that is the `SIRsigma` constraint proving the field decoded to the
-- index the indexed code demanded.  In the indexed presentation those
-- proofs were implicit in the family's index; here they are data.
public export
CbvIdAppEvidence : CbvDom CbvIdApp
CbvIdAppEvidence =
  (InSIR {c=(smallIIRtoIR CbvD)} (CbvIdApp **
     (cbvIdMu ** ((\_ => Refl) **
       (cbvIdMu ** ((\_ => Refl) **
         (cbvIdMu ** ((\_ => Refl) ** ())))))))
   ** Refl)

-- ... and it evaluates to the identity.
public export
cbvIdAppValue : cbvEval CbvIdApp CbvIdAppEvidence = CbvId
cbvIdAppValue = Refl



mutual
  public export
  T0StarterT : Type
  T0StarterT = Unit

  public export
  data T0MakerT : Type where
    T0Mk : Test0 -> Test0 -> T0MakerT

  public export
  data T0DepMakerT : Type where
    T0DepMk : (a : Test0) -> Test1 a -> Test1 a -> T0DepMakerT

  public export
  data Test0 : Type where
    T0Starter : T0StarterT -> Test0
    T0Maker : T0MakerT -> Test0
    T0DepMaker : T0DepMakerT -> Test0

  public export
  data T1StarterT : T0StarterT -> Type where
    T1Start : T1StarterT ()

  public export
  T1IdT : Test0 -> Type
  T1IdT _ = Unit

  public export
  data Test1 : Test0 -> Type where
    T1Starter : (t0s : T0StarterT) -> T1StarterT t0s -> Test1 (T0Starter t0s)
    T1Id : (a : Test0) -> T1IdT a -> Test1 a
    T1Maker :
      (a, b : Test0) -> Test1 a -> Test1 b -> Test1 (T0Maker $ T0Mk a b)
    T1Composer : (a, b, c : Test0) ->
      Test1 (T0Maker $ T0Mk b c) -> Test1 (T0Maker $ T0Mk a b) ->
      Test1 (T0Maker $ T0Mk a c)
    T1Distrib : (a, b, c : Test0) ->
      Test1 (T0Maker $ T0Mk a (T0Maker $ T0Mk b c)) ->
      Test1 (T0Maker $ T0Mk (T0Maker $ T0Mk a b) (T0Maker $ T0Mk a c))
    T1DepComposer :
      (a : Test0) -> (f, g, h : Test1 a) ->
      Test1 (T0DepMaker $ T0DepMk a g h) ->
      Test1 (T0DepMaker $ T0DepMk a f g) ->
      Test1 (T0DepMaker $ T0DepMk a f h)
    T1Telescope : (a : Test0) -> (f, g : Test1 a) ->
      (t, t' : Test1 (T0DepMaker $ T0DepMk a f g)) ->
      (dt, dt' :
        Test1 (T0DepMaker $ T0DepMk (T0DepMaker $ T0DepMk a f g) t t')) ->
      Test1
        (T0DepMaker $
          T0DepMk
            (T0DepMaker $ T0DepMk (T0DepMaker $ T0DepMk a f g) t t') dt dt')

--------------------------------------------
--------------------------------------------
---- Finitary inductive-inductive types ----
--------------------------------------------
--------------------------------------------

t0Starter : FinIndIndF1Constr
t0Starter = FII1c 0 0 []

t0Maker : FinIndIndF1Constr
t0Maker = FII1c 2 0 []

t0DepMaker : FinIndIndF1Constr
t0DepMaker = FII1c 1 2 [ FZ, FZ ]

T0F : FinIndIndF1
T0F = FII1 [ t0Starter, t0Maker, t0DepMaker ]

t1Starter : FinIndIndF2Constr T0F
t1Starter = FII2c 0 0 FF2AZ $ FF2t1a (FZ ** [] ** [])

t1Id : FinIndIndF2Constr T0F
t1Id = FII2c 1 0 FF2AZ $ FF2t1p FZ

t1Maker : FinIndIndF2Constr T0F
t1Maker = FII2c 2 2 (FF2AS (FF2AS FF2AZ $ FF2t1p FZ) $ FF2t1p $ FS FZ) $
  FF2t1a (FS FZ ** [FF2t1p FZ, FF2t1p $ FS FZ] ** [])

t1Telescope : FinIndIndF2Constr T0F
t1Telescope = FII2c 1 6
  (FF2AS (FF2AS (FF2AS (FF2AS (FF2AS (FF2AS FF2AZ
    $ FF2t1p FZ)
    $ FF2t1p FZ)
    $ FF2t1a ((FS (FS FZ)) **
      [FF2t1p FZ] **
      [?t1Telescope_FF2t2hd_hole, ?t1Telescope_FF2t2tl_hole]))
    $ ?t1Telescope_hole_tel_4)
    $ ?t1Telescope_hole_tel_5)
    $ ?t1Telescope_hole_tel_6) $
  ?t1Telescope_hole_param

T1F : FinIndIndF2 T0F
T1F = FII2 [ t1Starter, t1Id, t1Maker, t1Telescope ]

T01F : FinIndInd
T01F = (T0F ** T1F)

T0 : Type
T0 = FinIndIndMu1 T01F

T1 : T0 -> Type
T1 = FinIndIndMu2 T01F

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
polyIndTypesTest : IO ()
polyIndTypesTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin PolyIndTypesTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "---------------------"
  putStrLn "End PolyIndTypesTest."
  putStrLn "====================="
  pure ()
