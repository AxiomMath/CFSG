module

public import Certificates.Data.Kernel.RouteP.RigidTwin
public import Certificates.Kernel.RouteP.Text.PlanesX
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CertificateChecks.KernelRouteP

open CFSG.KC.RouteP CFSG.KD.RouteP CFSG.KS.PK

@[expose] noncomputable def PGF (l x : Nat) : Nat := nIf(Nat.blt l (nat_lit 13), PGE l x, nat_lit 0)

@[expose] noncomputable def rgRun (r : Nat) : BS := BS.run PGF (List.range 13) 891 r

@[expose] noncomputable def rgRuns : List BS := [rgRun 0, rgRun 1, rgRun 12, rgRun 159]

@[expose] noncomputable def getK (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih k => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) k) l

@[expose] noncomputable def rgSnoc (l : List Nat) (x : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [x] (fun a _ ih => a :: ih) l

@[expose] noncomputable def rgLen (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def rgFold {β : Type} (f : β → Nat → β) (l : List Nat) (b : β) : β :=
  List.rec (motive := fun _ => β → β) (fun b => b) (fun x _ ih b => ih (f b x)) l b

@[expose] noncomputable def letterM (F : Nat → Nat → Nat) (h p : Nat) (st : BS × Nat) (l : Nat) :
    BS × Nat :=
  Bool.rec (⟨rgSnoc st.1.pts (F l p), rgSnoc st.1.par h, rgSnoc st.1.lab l⟩,
      Nat.lor st.2 (Nat.shiftLeft 1 (F l p))) st
    (Nat.blt 0 (Nat.land st.2 (Nat.shiftLeft 1 (F l p))))

@[expose] noncomputable def stepM (F : Nat → Nat → Nat) (lv : List Nat) (st : BS × Nat) (h : Nat) :
    BS × Nat :=
  Bool.rec st (rgFold (letterM F h (getK st.1.pts h)) lv st) (Nat.blt h (rgLen st.1.pts))

@[expose] noncomputable def runM (F : Nat → Nat → Nat) (lv : List Nat) (n r : Nat) : BS × Nat :=
  rgFold (stepM F lv) (List.range n) (⟨[r], [0], [0]⟩, Nat.shiftLeft 1 r)

@[expose] noncomputable def rgRunK (r : Nat) : BS := (runM PGF (List.range 13) 891 r).1

@[expose] noncomputable def rgRunsK : List BS := [rgRunK 0, rgRunK 1, rgRunK 12, rgRunK 159]

@[expose] noncomputable def rgMask (r : Nat) : Nat := (runM PGF (List.range 13) 891 r).2

@[expose] noncomputable def obStep (F : Nat → Nat → Nat) (m n : Nat) (st : Nat × List BS) (r : Nat) :
    Nat × List BS :=
  Bool.rec (Nat.lor st.1 (runM F (List.range m) n r).2, st.2 ++ [(runM F (List.range m) n r).1]) st
    (Nat.blt 0 (Nat.land st.1 (Nat.shiftLeft 1 r)))

@[expose] noncomputable def orbitBSM (F : Nat → Nat → Nat) (m n : Nat) : List BS :=
  ((List.range n).foldl (obStep F m n) (0, ([] : List BS))).2

@[expose] noncomputable def idxK (y : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Bool.rec (Nat.succ ih) 0 (Nat.beq x y)) l

@[expose] noncomputable def propLFK (F : Nat → Nat → Nat) (s : BS) (c : Nat) (f : Nat) :
    Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => c)
    (fun _ ih k => Bool.rec c (F (getK s.lab k) (ih (getK s.par k)))
      (Bool.and (Nat.blt 0 k) (Nat.blt (getK s.par k) k))) f

@[expose] noncomputable def candTwK (F : Nat → Nat → Nat) (m : Nat) (s : BS) (c : Nat) : Bool :=
  (List.range s.pts.length).all fun k => (List.range m).all fun l =>
    propLFK F s c (idxK (F l (getK s.pts k)) s.pts) (idxK (F l (getK s.pts k)) s.pts) ==
      F l (propLFK F s c k k)

@[expose] noncomputable def interK (a b : Nat) : Nat :=
  ((List.range 24).filter fun m => (List.range 24).any fun j => PXE b j == PXE a m).length

@[expose] noncomputable def nodupM (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih m => Bool.rec false (ih (Nat.lor m (Nat.shiftLeft 1 x)))
      (Nat.beq (Nat.land (Nat.shiftRight m x) 1) 0)) l

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rg_roots :
    ((orbitBSM PGF 13 891).map (fun s => s.pts.headD 0) == [0, 1, 12, 159]) = true := by
  decide +kernel

theorem rg_sizes : (rgRunsK.map (fun s => s.pts.length) == [1, 336, 512, 42]) = true := by
  decide +kernel

theorem rg_cover : Nat.beq (Nat.lor (Nat.lor (rgMask 0) (rgMask 1)) (Nat.lor (rgMask 12) (rgMask 159)))
    (Nat.sub (Nat.shiftLeft 1 891) 1) = true := by
  decide +kernel

theorem rg_root0 : ((rgRunK 0).pts.tail == []) = true := by
  decide +kernel

theorem rg_cand1 : ((rgRunK 1).pts.tail.filter (candTwK PGF 13 (rgRunK 1)) == []) = true := by
  decide +kernel

theorem rg_cand12 :
    ((rgRunK 12).pts.tail.filter (candTwK PGF 13 (rgRunK 12)) == []) = true := by
  decide +kernel

theorem rg_cand159 :
    ((rgRunK 159).pts.tail.filter (candTwK PGF 13 (rgRunK 159)) == [590]) = true := by
  decide +kernel

theorem rg_sep : (interK (combinedTw PGF rgRunsK [0, 1, 12, 590] 1)
    (combinedTw PGF rgRunsK [0, 1, 12, 590] 588) != interK 1 588) = true := by
  decide +kernel

theorem rg_nodup : ((List.range 13).all fun s => nodupM ((List.range 891).map (PGE s)) 0) = true := by
  decide +kernel

end CertificateChecks.KernelRouteP
