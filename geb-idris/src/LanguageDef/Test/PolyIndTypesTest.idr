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

mutual
  public export
  data IRCode : Type where
    IRCnat : IRCode
    IRCsigma : (u : IRCode) -> (IRdecode u -> IRCode) -> IRCode
    IRCpi : (u : IRCode) -> (IRdecode u -> IRCode) -> IRCode

  public export
  IRdecode : IRCode -> Type
  IRdecode IRCnat = Nat
  IRdecode (IRCsigma u f) = Sigma {a=(IRdecode u)} (IRdecode . f)
  IRdecode (IRCpi u f) = Pi {a=(IRdecode u)} (IRdecode . f)

mutual
  public export
  partial
  data IRCode' : Type where
    IRCnat' :
      IRCode'
    IRCsigma' :
      (u : IRCode') -> ((t : IRTerm ** IRfib t = u) -> IRCode') -> IRCode'
    IRCpi' :
      (u : IRCode') -> ((t : IRTerm ** IRfib t = u) -> IRCode') -> IRCode'

  public export
  partial
  data IRTerm : Type where
    IRTnat :
      Nat -> IRTerm
    IRTsigma :
      (u : IRCode') -> (v : (t : IRTerm ** IRfib t = u) -> IRCode') ->
      (t : IRTerm) -> (e : IRfib t = u) ->
      (t' : IRTerm) -> (IRfib t' = v (t ** e)) ->
      IRTerm
    IRTpi :
      (u : IRCode') -> (v : (t : IRTerm ** IRfib t = u) -> IRCode') ->
      ((t : IRTerm) -> (e : IRfib t = u) ->
       (t' : IRTerm ** (IRfib t' = v (t ** e)))) ->
      IRTerm

  public export
  partial
  IRfib : IRTerm -> IRCode'
  IRfib (IRTnat _) = IRCnat'
  IRfib (IRTsigma u v _ _ _ _) = IRCsigma' u v
  IRfib (IRTpi u v _) = IRCpi' u v

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


----------------------------------------------
----------------------------------------------
---- The fibre over a natural-number code ----
----------------------------------------------
----------------------------------------------

public export
partial
natFibTo : Nat -> IRFib IRCnat'
natFibTo n = (IRTnat n ** Refl)

public export
partial
natFibFrom : IRFib IRCnat' -> Nat
natFibFrom (IRTnat n ** _) = n

public export
partial
natFibToFrom : (z : IRFib IRCnat') -> natFibTo (natFibFrom z) = z
natFibToFrom (IRTnat _ ** Refl) = Refl

public export
partial
natFibIso : TIso Nat (IRFib IRCnat')
natFibIso = MkTIso natFibTo natFibFrom (\_ => Refl) natFibToFrom


---------------------------------------------
---------------------------------------------
---- The fibre over a dependent-sum code ----
---------------------------------------------
---------------------------------------------

public export
partial
sigmaPair : (u : IRCode') -> (v : IRFib u -> IRCode') ->
  (x : IRFib u) -> IRFib (v x) -> IRFib (IRCsigma' u v)
sigmaPair u v (t ** e) (t' ** e') = (IRTsigma u v t e t' e' ** Refl)

-- Matching the equality proof against `Refl` is what inverts the
-- constructor:  it forces the (higher-order) index `v` as well as `u`.
public export
partial
sigmaFst : (u : IRCode') -> (v : IRFib u -> IRCode') ->
  IRFib (IRCsigma' u v) -> IRFib u
sigmaFst u v (IRTsigma u v t e _ _ ** Refl) = (t ** e)

public export
partial
sigmaSnd : (u : IRCode') -> (v : IRFib u -> IRCode') ->
  (z : IRFib (IRCsigma' u v)) -> IRFib (v (sigmaFst u v z))
sigmaSnd u v (IRTsigma u v _ _ t' e' ** Refl) = (t' ** e')

public export
partial
sigmaEta : (u : IRCode') -> (v : IRFib u -> IRCode') ->
  (z : IRFib (IRCsigma' u v)) ->
  sigmaPair u v (sigmaFst u v z) (sigmaSnd u v z) = z
sigmaEta u v (IRTsigma u v _ _ _ _ ** Refl) = Refl

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
sigmaFibFromPair u v b j (_ ** _) (_ ** _) = Refl

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
piLam u v g = (IRTpi u v (\t, e => g (t ** e)) ** Refl)

public export
partial
piApp : (u : IRCode') -> (v : IRFib u -> IRCode') ->
  IRFib (IRCpi' u v) -> (x : IRFib u) -> IRFib (v x)
piApp u v (IRTpi u v g ** Refl) (t ** e) = g t e

public export
partial
piBeta : (u : IRCode') -> (v : IRFib u -> IRCode') ->
  (g : (x : IRFib u) -> IRFib (v x)) -> (x : IRFib u) ->
  piApp u v (piLam u v g) x = g x
piBeta u v g (_ ** _) = Refl

public export
partial
piEta : (u : IRCode') -> (v : IRFib u -> IRCode') ->
  (h : IRFib (IRCpi' u v)) -> piLam u v (piApp u v h) = h
piEta u v (IRTpi u v _ ** Refl) = Refl

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
  IRtoC fext IRCnat = IRCnat'
  IRtoC fext (IRCsigma u f) =
    IRCsigma' (IRtoC fext u)
      (\w => IRtoC fext (f (tiFrom (IRdecIso fext u) w)))
  IRtoC fext (IRCpi u f) =
    IRCpi' (IRtoC fext u)
      (\w => IRtoC fext (f (tiFrom (IRdecIso fext u) w)))

  public export
  partial
  IRdecIso : (fext : FunExt) -> (u : IRCode) ->
    TIso (IRdecode u) (IRFib (IRtoC fext u))
  IRdecIso fext IRCnat = natFibIso
  IRdecIso fext (IRCsigma u f) =
    tisoTrans
      (sigmaCongFrom (IRdecIso fext u) (\x => IRdecode (f x)))
      (sigmaFibIso
        (IRtoC fext u)
        (\w => IRtoC fext (f (tiFrom (IRdecIso fext u) w)))
        (\w => IRdecode (f (tiFrom (IRdecIso fext u) w)))
        (\w => IRdecIso fext (f (tiFrom (IRdecIso fext u) w))))
  IRdecIso fext (IRCpi u f) =
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
isNatC : IRCode' -> Bool
isNatC IRCnat' = True
isNatC (IRCsigma' _ _) = False
isNatC (IRCpi' _ _) = False

public export
partial
isSigmaC : IRCode' -> Bool
isSigmaC IRCnat' = False
isSigmaC (IRCsigma' _ _) = True
isSigmaC (IRCpi' _ _) = False

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
IRCsigmaCong : FunExt -> (u1 : IRCode) -> (f1 : IRdecode u1 -> IRCode) ->
  (u2 : IRCode) -> (f2 : IRdecode u2 -> IRCode) -> (p : u1 = u2) ->
  ((x : IRdecode u1) -> f1 x = f2 (replace {p=IRdecode} p x)) ->
  IRCsigma u1 f1 = IRCsigma u2 f2
IRCsigmaCong fext u f1 u f2 Refl q = cong (IRCsigma u) (funExt q)

public export
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
  IRcodeInv fext IRCnat' = IRCnat
  IRcodeInv fext (IRCsigma' a v) =
    IRCsigma (IRcodeInv fext a)
      (\x => IRcodeInv fext
        (v (replace {p=IRFib} (IRcodeInvEq fext a)
             (tiTo (IRdecIso fext (IRcodeInv fext a)) x))))
  IRcodeInv fext (IRCpi' a v) =
    IRCpi (IRcodeInv fext a)
      (\x => IRcodeInv fext
        (v (replace {p=IRFib} (IRcodeInvEq fext a)
             (tiTo (IRdecIso fext (IRcodeInv fext a)) x))))

  public export
  partial
  IRcodeInvEq : (fext : FunExt) -> (a : IRCode') ->
    IRtoC fext (IRcodeInv fext a) = a
  IRcodeInvEq fext IRCnat' = Refl
  IRcodeInvEq fext (IRCsigma' a v) =
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
  IRcodeInvEq fext (IRCpi' a v) =
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
  IRtoCinj fext IRCnat IRCnat _ = Refl
  IRtoCinj fext IRCnat (IRCsigma _ _) eq = absurd (cong isNatC eq)
  IRtoCinj fext IRCnat (IRCpi _ _) eq = absurd (cong isNatC eq)
  IRtoCinj fext (IRCsigma _ _) IRCnat eq = absurd (cong isNatC eq)
  IRtoCinj fext (IRCpi _ _) IRCnat eq = absurd (cong isNatC eq)
  IRtoCinj fext (IRCsigma _ _) (IRCpi _ _) eq = absurd (cong isSigmaC eq)
  IRtoCinj fext (IRCpi _ _) (IRCsigma _ _) eq = absurd (cong isSigmaC eq)
  IRtoCinj fext (IRCsigma u1 f1) (IRCsigma u2 f2) eq =
    IRCsigmaCong fext u1 f1 u2 f2
      (IRsigmaInjBase fext u1 f1 u2 f2 eq)
      (IRsigmaInjStep fext u1 f1 u2 f2 eq)
  IRtoCinj fext (IRCpi u1 f1) (IRCpi u2 f2) eq =
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
