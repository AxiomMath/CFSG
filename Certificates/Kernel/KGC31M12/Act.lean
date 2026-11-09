module

public import Certificates.Kernel.KGC31M12.Defs
public import Certificates.Data.Kernel.KGC31PSplit
public import CFSG.Certificates.Kernel.KGC31PLazy
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M12

open CFSG.KC.Enum CFSG.KS CFSG.KC.KGC31P

@[expose] noncomputable def actR (x : Nat) : Bool :=
  ((List.range 5).all fun a => pactOne 12 4 5 (ppw 12 4 X5 a) x) &&
    (List.range 11).all fun a => pactOne 12 4 11 (ppw 12 4 X11 a) x

@[expose] noncomputable def actF (x : Nat) : Bool :=
  !allN 12 (fun i => Nat.beq (pg 4 (mask 4) x (pg 4 (mask 4) x i)) i) || actR x

@[expose] noncomputable def actL (g t : Nat) : Bool :=
  !allN 12 (fun i => Nat.beq (pgL 12 4 g t (pgL 12 4 g t i)) i) || actR (pc 12 4 g t)

@[expose] noncomputable def actPiece (i : Nat) : Bool :=
  pallL 12 4 actL TL.tail (pc 12 4 (pidn 12 4) ((TL.headD []).getD i 0))

theorem kTL0 : Nat.beq (TL.headD []).length 12 = true := by quickRfl

theorem kTLne : (!TL.isEmpty) = true := by quickRfl

theorem kTLtl : (!TL.tail.isEmpty) = true := by quickRfl

end CertificateChecks.KernelKGC31M12

#kc_each CertificateChecks.KernelKGC31M12.actPiece 0 12

namespace CertificateChecks.KernelKGC31M12

open CFSG.KC.Enum CFSG.KS CFSG.KC.KGC31P

#kc_forall_chunks actPieces (fun i => actPiece i = true) 12 CertificateChecks.KernelKGC31M12.actPiece 1

theorem actL_eq (g t : Nat) : actL g t = actF (pc 12 4 g t) := by
  unfold actL actF
  simp only [pgL_eq (n := 12) (w := 4) (by decide)]

theorem actAllF : pallProducts 12 4 actF TL (pidn 12 4) = true := by
  rw [eq_headD_cons kTLne]
  apply pall_of_pieces
  intro i hi
  rw [Nat.eq_of_beq_eq_true kTL0] at hi
  rw [← pallL_eq 12 4 actL_eq _ _ (ne_nil_of_isEmpty kTLtl)]
  exact actPieces i hi

theorem all_range_swap (m : Nat) (P : Nat → Nat → Bool) (l : List Nat) :
    (List.range m).all (fun a => l.all (P a)) = l.all fun x => (List.range m).all fun a => P a x := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true]
  exact ⟨fun h x hx a ha => h a ha x hx, fun h a ha x hx => h x hx a ha⟩

theorem actAll_of_R {m X : Nat}
    (hQ : ∀ x, actR x = true → ((List.range m).all fun a => pactOne 12 4 m (ppw 12 4 X a) x) = true) :
    actAll m X = true := by
  unfold actAll
  rw [all_range_swap, I, pfilter_all, List.all_nil, Bool.true_and]
  refine pall_mono 12 4 (fun x hx => ?_) TL (pidn 12 4) actAllF
  try dsimp only
  unfold actF at hx
  rw [Bool.or_eq_true] at hx ⊢
  rcases hx with hx | hx
  · left
    cases hp : pord 12 4 2 x
    · rfl
    · rw [pord2_pt (n := 12) (w := 4) ⟨by decide, by decide⟩ hp] at hx
      exact absurd hx (by decide)
  · exact Or.inr (hQ x hx)

end CertificateChecks.KernelKGC31M12

end
