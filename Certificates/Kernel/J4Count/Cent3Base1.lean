
module


public import Certificates.Kernel.J4Count.Cent3Checks
public import Certificates.Kernel.J4Count.FixCEEltBase1
public import CFSG.Certificates.Kernel.J4FiveSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4QuotBase

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.FixCE

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4M2 CFSG.KC.J4Cent3 CFSG.KC.J4Five CFSG.KC.J4Q
open CFSG.KD.J4FixCE CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs CertificateChecks.KernelJ4Count.Cent3
open Equiv

theorem starOK_cE {i : ℕ} (hi : i < 24) : StarOK cE i (getN 0 ZE i) := by
  intro m hm
  have h := allN_spec ce_tab i hi
  beta_reduce at h
  refine ⟨CFSG.KS.SporSch.C11.appK PC m, ?_, ?_⟩
  · have key : ∀ (L : List ℕ), List.rec (motive := fun _ => Bool) true
        (fun c _ ih => andB (memK (CFSG.KS.SporSch.C11.appK PC c)
          (starMasks.getD (getN 0 ZE i) [])) ih) L = true → ∀ c ∈ L,
        CFSG.KS.SporSch.C11.appK PC c ∈ starMasks.getD (getN 0 ZE i) [] := by
      intro L
      induction L with
      | nil => intro _ c hc; exact absurd hc List.not_mem_nil
      | cons c L ih =>
        intro hL c' hc'
        change andB _ _ = true at hL
        rw [CFSG.KC.J4Q.andB_eq, Bool.and_eq_true] at hL
        rcases List.mem_cons.1 hc' with rfl | hc'
        · have mk : ∀ (x : ℕ) (L : List ℕ), memK x L = true → x ∈ L := by
            intro x L
            induction L with
            | nil => intro h; exact absurd h Bool.false_ne_true
            | cons y L ih2 =>
              intro h
              change orB (Nat.beq x y) _ = true at h
              rw [orB_eq_or, Bool.or_eq_true] at h
              rcases h with h | h
              · rw [Nat.eq_of_beq_eq_true h]; exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (ih2 h)
          exact mk _ _ hL.1
        · exact ih hL.2 c' hc'
    exact key _ h m hm
  · rw [cE_conj_eta, CC, CFSG.KS.SporSch.C11.app_eq]

end CertificateChecks.KernelJ4Count.FixCE

end
