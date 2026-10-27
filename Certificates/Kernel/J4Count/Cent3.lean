
module

public import Certificates.Kernel.J4Count.Cent3Base1

public import Certificates.Kernel.J4Count.FixCEElt
public import Certificates.Kernel.J4Count.FiveM24
public import CFSG.Certificates.Kernel.J4Cent3Sound
public import Certificates.Kernel.J4Count.Cent3Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.FixCE

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4M2 CFSG.KC.J4Cent3 CFSG.KC.J4Five CFSG.KC.J4Q
open CFSG.KD.J4FixCE CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs CertificateChecks.KernelJ4Count.Cent3
open Equiv

theorem pf_ceBar : ∀ i < 24, pf (Stars.starHom ⟨cE, cE_mem_Hj⟩) i = getN 0 ZE i := by
  intro i hi
  rw [pf_fin' _ hi]
  have e := Stars.starMap_eq (g := ⟨cE, cE_mem_Hj⟩) (i := ⟨i, hi⟩) (i' := ⟨getN 0 ZE i, ZE_lt hi⟩)
    (starOK_cE hi)
  exact congrArg Fin.val e

theorem card_cent_ceBar : Nat.card ↥(Five.G24 ⊓ Subgroup.centralizer
    ({Stars.starHom ⟨cE, cE_mem_Hj⟩} : Set (Perm (Fin 24)))) ≤ 1080 := by
  have hmem : Stars.starHom ⟨cE, cE_mem_Hj⟩ ∈ Five.G24 := by
    rw [← Five.range_eq]
    exact ⟨_, rfl⟩
  have h4 : cand3N GB GP ZE CRD3 FL3 TL3 = 1 := Nat.eq_of_beq_eq_true ce_cand
  have h6 : ∀ x ∈ FL3 ++ TL3, x < 24 := by
    intro x hx
    simp only [FL3, TL3, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    omega
  have hlen : GP.length = GB.length := rfl
  have hB : GB.length = 12 := rfl
  have hF : FL3 = [0, 1, 5, 15, 17, 22] := rfl
  have hT : TL3 = [4, 6, 7, 2, 12, 10] := rfl
  exact card_cent3_le Five.G24 hF hT hlen hB Five.gold_inv Five.gen_G24 hmem pf_ceBar ce_fix ce_oct
    ce_crd h4 ce_dist h6

theorem card_cent_H_le :
    Nat.card ↥(Subgroup.centralizer {cE} ⊓ CFSG.Sporadic.J4Schreier.H) ≤ 34560 := by
  rw [H_eq_Hj]
  have hE : Nat.card ↥(Subgroup.centralizer ({cE} : Set J) ⊓ Eg uJ 11) ≤ 32 := by
    rw [inf_comm, card_cent_E]
  exact Five.card_centralizer_Hj_le' (m := 1080) (n := 32) cE_mem_Hj hE card_cent_ceBar

end CertificateChecks.KernelJ4Count.FixCE

end
