
module

public import Certificates.Kernel.He7223.GlueCent

public section

set_option maxRecDepth 400000

#kss_strof CertificateChecks.KernelHe7223.NSS CFSG.Quasithin.KGC31.He.nsW
#kss_strof CertificateChecks.KernelHe7223.N7S CFSG.Quasithin.KGC31.He.n7W
#kss_strof CertificateChecks.KernelHe7223.NJS CFSG.Quasithin.KGC31.He.njW
#kss_strof CertificateChecks.KernelHe7223.Y5S CFSG.Quasithin.KGC31.He.y5W

namespace CertificateChecks.KernelHe7223

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.WordPts CFSG.KC.OrbPath
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CertificateChecks.KernelLC.HeFix
  CertificateChecks.KernelSchreierFam.He725

theorem nsW_eq : nsW.getD 6 [] = gw 0 ∧ nsW.getD 11 [] = gw 1 := by
  rw [NSS.eq, decodeWs_ofList (by decide) (ascii_of_all (by decide +kernel))]
  decide +kernel

theorem n7W_eq : n7W.getD 3 [] = gw 2 ∧ n7W.getD 9 [] = gw 3 := by
  rw [N7S.eq, decodeWs_ofList (by decide) (ascii_of_all (by decide +kernel))]
  decide +kernel

theorem njW_eq : njW = [gw 4, gw 5] := by
  rw [NJS.eq, decodeWs_ofList (by decide) (ascii_of_all (by decide +kernel))]
  decide +kernel

theorem y5W_eq : y5W = gw 6 := by
  rw [Y5S.eq, decodeW_ofList]
  decide +kernel

theorem lsGenW_eq : lsGenW = [lg 0, lg 1, lg 2] := by
  rw [lsGenW, y5W_eq, njW_eq]
  decide +kernel

theorem LG_letters : ∀ j < 3, lettersOK 2 (lg j) = true := by decide +kernel

theorem GW_letters2 : ∀ j < 7, lettersOK 2 (gw j) = true := by decide +kernel

theorem andB_true {a b : Bool} (h : CFSG.KLie.CT.andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

theorem orderOf_y5 :
    orderOf (elt y5W) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [y5W_eq]
  obtain ⟨h5, h1⟩ := andB_true ch7223y5
  have hm : elt (gw 6) ∈ heP := elt_mem_heP (GW_letters2 6 (by norm_num))
  have hl : ∀ wd ∈ [gw 6, gw 6, gw 6, gw 6, gw 6], lettersOK gens3.length wd = true := by
    intro wd hw
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hw
    subst hw
    exact GW_letters 6 (by norm_num)
  apply orderOf_eq_prime
  · have hpt := fixPtsK_sound letRep_LU hl h5
    refine eq_of_pts (bsL_eq ▸ baseFaithful_heP) (heP.pow_mem hm 5) heP.one_mem fun p hp => ?_
    have := hpt p hp
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    have e5 : elt (gw 6) ^ 5 = elt (gw 6) * (elt (gw 6) * (elt (gw 6) * (elt (gw 6) *
        elt (gw 6)))) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [Equiv.Perm.one_apply, e5]
    exact this
  · intro he
    have := fixPtsK_of_prod_eq_one letRep_LU (gw_mem (j := 6) (by norm_num))
      (by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          exact he) bsL_lt
    rw [this] at h1
    exact absurd h1 (by decide)

theorem eW_len : eW.length = 6 := by rw [eW_eq]; decide +kernel

theorem qW_len : qW.length = 4 := by rw [qW_eq]; decide +kernel

theorem eW_letters3 : ∀ wd ∈ eW, lettersOK gens3.length wd = true := by
  rw [eW_eq]; exact letters3 EB_letters

theorem qW_letters3 : ∀ wd ∈ qW, lettersOK gens3.length wd = true := by
  rw [qW_eq]; exact letters3 QB_letters

theorem eW_mem :
    ∀ wd ∈ eW, evalSignedWord gens3 wd ∈ heP := by
  rw [eW_eq]; exact mem_heP_of EB_letters

theorem qW_mem :
    ∀ wd ∈ qW, evalSignedWord gens3 wd ∈ heP := by
  rw [qW_eq]; exact mem_heP_of QB_letters

theorem mem_eNorm_E {g : List ℤ}
    (hg : lettersOK 2 g = true) {M : ℕ} (h : matE g M = true) : elt g ∈ eNorm ebasis_E := by
  have h' : matK 8330 14 LU LUI bsL eW 6 g M = true := by rw [eW_eq]; exact h
  exact mem_eNorm_of_matK (bsL_eq ▸ baseFaithful_heP) letRep_LU eW_letters3 eW_mem eW_len
    ebasis_E (lettersOK_mono (by rw [gens3_length]; norm_num) hg) (elt_mem_heP hg) h'

theorem mem_eNorm_Q {g : List ℤ}
    (hg : lettersOK 2 g = true) {M : ℕ} (h : matQ g M = true) : elt g ∈ eNorm ebasis_Q := by
  have h' : matK 8330 14 LU LUI bsL qW 4 g M = true := by rw [qW_eq]; exact h
  exact mem_eNorm_of_matK (bsL_eq ▸ baseFaithful_heP) letRep_LU qW_letters3 qW_mem qW_len
    ebasis_Q (lettersOK_mono (by rw [gens3_length]; norm_num) hg) (elt_mem_heP hg) h'

theorem nsGen_mem_eNorm :
    elt (nsW.getD 6 []) ∈ eNorm ebasis_E ∧ elt (nsW.getD 11 []) ∈ eNorm ebasis_E := by
  rw [nsW_eq.1, nsW_eq.2]
  exact ⟨mem_eNorm_E (GW_letters2 0 (by norm_num)) ch7223mNs0,
    mem_eNorm_E (GW_letters2 1 (by norm_num)) ch7223mNs1⟩

theorem n7Gen_mem_eNorm :
    elt (n7W.getD 3 []) ∈ eNorm ebasis_Q ∧ elt (n7W.getD 9 []) ∈ eNorm ebasis_Q := by
  rw [n7W_eq.1, n7W_eq.2]
  exact ⟨mem_eNorm_Q (GW_letters2 2 (by norm_num)) ch7223mN70,
    mem_eNorm_Q (GW_letters2 3 (by norm_num)) ch7223mN71⟩

theorem nj_mem_eNorm :
    ∀ n ∈ njW, elt n ∈ eNorm ebasis_E := by
  rw [njW_eq]
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact mem_eNorm_E (GW_letters2 4 (by norm_num)) ch7223mNj0
  · exact mem_eNorm_E (GW_letters2 5 (by norm_num)) ch7223mNj1

theorem lsGen_mem_eNorm :
    ∀ w ∈ lsGenW, elt w ∈ eNorm ebasis_E := by
  rw [lsGenW_eq]
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact mem_eNorm_E (LG_letters 0 (by norm_num)) ch7223mL0
  · exact mem_eNorm_E (LG_letters 1 (by norm_num)) ch7223mL1
  · exact mem_eNorm_E (LG_letters 2 (by norm_num)) ch7223mL2

theorem y5_mem_eNorm :
    elt y5W ∈ eNorm ebasis_E :=
  lsGen_mem_eNorm _ (by rw [lsGenW]; exact List.mem_cons_self)

end CertificateChecks.KernelHe7223

end
