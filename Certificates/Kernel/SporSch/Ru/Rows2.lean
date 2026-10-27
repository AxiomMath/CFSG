module

public import CFSG.Certificates.Kernel.SporSch.RuEnumSound
public import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs

public section

namespace CertificateChecks.KernelSporSch.Rows2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem unpack_inj {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) (h : unpack n w p = unpack n w q) : p = q := by
  have e := canon_eqA hp hq
  rw [h, eqK_sound (n := n) (w := w) (Nat.beq_refl q)] at e
  exact Nat.eq_of_beq_eq_true e.symm

theorem all2_mono {n : Nat} {L : Array Level} {p q : Array Nat → Bool}
    (h : all2 n L p = true) (hpq : ∀ g, p g = true → q g = true) : all2 n L q = true := by
  unfold all2 at h ⊢
  rw [allLt_iff] at h ⊢
  intro a ha
  have h1 := h a ha
  rw [allLt_iff] at h1 ⊢
  exact fun b hb => hpq _ (h1 b hb)

theorem all2_of_rows_imp {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {p : Array Nat → Bool} {pK : Nat → Bool}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (h2 : 2 ≤ nb)
    (hpK : ∀ G, canonK n w (mask w) (n * w) G = true → pK G = true → p (unpack n w G) = true)
    (h : ∀ a < rcnt (LR 0), row2K n w (mask w) (n * w) LR TR pK a = true) :
    all2 n (rawLevels n S base) p = true := by
  classical
  have h1 := all2_of_rows (p := fun g => decide (∃ G, canonK n w (mask w) (n * w) G = true ∧
      unpack n w G = g ∧ pK G = true)) hb hp hl h2 (fun G hG => ?_) h
  · exact all2_mono h1 fun g hg => by
      obtain ⟨G, hc, rfl, hk⟩ := of_decide_eq_true hg
      exact hpK G hc hk
  · cases e : pK G
    · refine (decide_eq_false ?_).symm
      rintro ⟨G', hc', hu, hk'⟩
      rw [unpack_inj hc' hG hu, e] at hk'
      exact Bool.false_ne_true hk'
    · exact (decide_eq_true ⟨G, hG, rfl, e⟩).symm

end CertificateChecks.KernelSporSch.Rows2

end
