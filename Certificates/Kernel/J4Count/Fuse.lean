
module


public import Certificates.Kernel.J4Count.FixZK
public import Certificates.Kernel.J4Count.FuseBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.Fuse

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.Sporadic.J4Schreier
open CFSG.Quasithin.H13.J4 (uP vP dP tP cnjP conjEqP lettersOK)

theorem tS_eq_tJ' : CFSG.Quasithin.H13.J4Classes.tS = CFSG.Quasithin.H13.J4.tJ := by
  refine Subtype.ext ?_
  have hu : (CFSG.Quasithin.H13.J4Classes.uS : GL (Fin 112) (ZMod 2)) = CFSG.Quasithin.H13.J4.u := by
    rw [CFSG.Quasithin.H13.J4Classes.uS, CFSG.Quasithin.H13.J4Classes.coe_signedWord_ab _
      (CFSG.Quasithin.H13.J4Classes.letters_ok_of uLetters_ok), CFSG.Quasithin.H13.J4.u_eq_wordProd]
  have hv : (CFSG.Quasithin.H13.J4Classes.vS : GL (Fin 112) (ZMod 2)) = CFSG.Quasithin.H13.J4.v := by
    rw [CFSG.Quasithin.H13.J4Classes.vS, CFSG.Quasithin.H13.J4Classes.coe_signedWord_ab _
      (CFSG.Quasithin.H13.J4Classes.letters_ok_of vLetters_ok), CFSG.Quasithin.H13.J4.v_eq_wordProd]
  rw [CFSG.Quasithin.H13.J4Classes.tS, CFSG.Quasithin.H13.J4.tJ_coe, CFSG.Quasithin.H13.J4.t, CFSG.Quasithin.H13.J4.d,
    SubgroupClass.coe_pow, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    hu, hv]

theorem w_ok {w : List Int} (hw : lettersOK w = true) : PairOK (wordP An Bn w) (wK w).1 (wK w).2 :=
  wordP_ok' hK a_ok b_ok w (CFSG.Quasithin.H13.J4Classes.letters_ok_of hw)

theorem tP_ok : PairOK tP TK.1 TK.2 :=
  ppow_ok (pm_ok (pm_ok (pm_ok (pinv_ok (w_ok vLetters_ok)) (w_ok uLetters_ok)) (w_ok vLetters_ok))
    (w_ok uLetters_ok)) 22

theorem cnj_ok {G E : Pair} {g e : Nat × Nat} (hG : PairOK G g.1 g.2) (hE : PairOK E e.1 e.2)
    (k : Nat) : PairOK (cnjP G E k) (cnK g e k).1 (cnK g e k).2 :=
  pm_ok hG (ppow_ok (pm_ok (pm_ok (pm_ok (pinv_ok hG) tP_ok) hG) hE) k)

theorem fusion_z : conjEqP (cnjP (mulP Bn An) Zn 3) Zn = true := by
  have hC := cnj_ok (pm_ok (p := (B, Bi)) (q := (A, A)) b_ok a_ok) z_ok 3
  have hL := pm_ok (pm_ok (pinv_ok hC) tP_ok) hC
  have e := enc_inj hL.1.1 z_ok.1.1 (by rw [hL.1.2, z_ok.1.2]; exact Nat.eq_of_beq_eq_true fuse)
  change ((mulP (mulP (invP (cnjP (mulP Bn An) Zn 3)) tP) (cnjP (mulP Bn An) Zn 3)).1 == Zn.1) = true
  rw [e]
  exact beq_self_eq_true _

theorem isConj_tJ_z : IsConj CFSG.Quasithin.H13.J4.tJ z :=
  tS_eq_tJ' ▸ CFSG.Quasithin.H13.J4Classes.fusion_of_check
    (rep_mulP (rep_b CFSG.Sporadic.J4Schreier.matFacts) (rep_a CFSG.Sporadic.J4Schreier.matFacts))
    (rep_z CFSG.Sporadic.J4Schreier.matFacts) 3 fusion_z

theorem card_fix_tJ' :
    Nat.card {w : CFSG.Sporadic.J4.Row //
      w ∈ MulAction.orbit CFSG.Sporadic.J4.J v ∧ CFSG.Quasithin.H13.J4.tJ • w = w} = 52349 := by
  rw [CFSG.Sporadic.J4.Struct.card_fix_conj (MulAction.orbit CFSG.Sporadic.J4.J v)
    (fun g x hx => by obtain ⟨k, rfl⟩ := hx; exact ⟨g * k, mul_smul g k v⟩) isConj_tJ_z]
  exact card_fix_z

end CertificateChecks.KernelJ4Count.Fuse

end
