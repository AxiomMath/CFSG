
module

public import Certificates.Kernel.Sporadic.ONC.FinalBase

public import Certificates.Kernel.Sporadic.ONC.Sub
public import Certificates.Kernel.Sporadic.ONC.Chain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONC

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.ONC
open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm.Native CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.ON.Kernel
open CFSG.Sporadic.SmallF2.Native (lettersOf instrLt ordOK)

theorem sift_of {T : Table} {f : ℕ → ℕ} (hf : ∀ x < 245520, ap T x = f x)
    (hlt : ∀ x < 245520, f x < 245520) :
    sift (chainTrees nPts lettersT chainBase) lettersT chainQb chainQ 0 (apT T chainQ) = siftQ f := by
  rw [chain_eq.1]
  have h := sift_eq chain_hyp 3 0 (by norm_num) (apT T chainQ)
    (img_lt fun x hx => by rw [hf x hx]; exact hlt x hx)
  rw [img_toList hf] at h
  exact h

theorem orbitSizes_ok : orbitSizes (chainTrees nPts lettersT chainBase) = orbSizes := by
  obtain ⟨c0, c1, c2⟩ := tcnt_chain
  rw [chain_eq.1]
  simp only [orbitSizes, Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero, List.map_cons,
    List.map_nil, rec_size]
  rw [show ((0 : Fin 3) : ℕ) = 0 from rfl, c0]
  simp [c1, c2, orbSizes]

theorem chain_ok : chainChecks (orbitData ()) negN (runSLP nPts prog (regs0 (orbitData ()))).2
    lettersT (chainTrees nPts lettersT chainBase) 3 = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, sA, sB, sN, -⟩ := misc_parts
  unfold chainChecks
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, slp_facts.1⟩, ?_⟩, facts.2.2.2.2.2.1⟩, facts.2.2.2.2.2.2⟩, chain_eq.2 3⟩,
    orbitSizes_ok⟩, ?_⟩, ?_⟩, ?_⟩
  · decide
  · rw [Array.all_eq_true]
    intro i hi
    have hi' : i < 4 := hi
    interval_cases i <;> rfl
  · rw [sift_of (fun x hx => alpha_ap hx) (fun x hx => (tabs_lt hx).1)]
    exact sA
  · rw [sift_of (fun x hx => beta_ap hx) (fun x hx => (tabs_lt hx).2)]
    exact sB
  · rw [sift_of (fun x hx => negN_ap hx) (fun x hx => (neg_pt hx).1)]
    exact sN

theorem on_cert : onCertificate 3 = true := by
  unfold onCertificate
  dsimp only
  rw [invW_eq]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨facts.1, facts.2.1⟩, facts.2.2.1⟩, facts.2.2.2.1⟩, chain_ok⟩, line_ok⟩, sub_ok⟩,
    facts.2.2.2.2.1⟩, ord_ok⟩

end CertificateChecks.KernelSpor.ONC

end
