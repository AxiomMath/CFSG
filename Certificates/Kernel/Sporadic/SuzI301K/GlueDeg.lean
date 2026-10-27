module

public import Certificates.Kernel.Sporadic.SuzI301K.Deg
public import Certificates.Kernel.SuzA17321.Facts
public import Certificates.Kernel.LocalComp.B0SuzProof

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzI301K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin CFSG.KC.SuzI301K
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.RankThree.Native
open CFSG.Sporadic.SuzI301 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0 CFSG.PSL3Four.Native
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse

theorem band {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

theorem relK_spec {H XA D B2 B3 T1 TAU : Nat} (k : relK H XA D B2 B3 T1 TAU = true) :
    Nat.beq D (conjP H XA) = true ∧ commP T1 D = true ∧ commP T1 B2 = true ∧
    commP T1 B3 = true ∧ commP T1 TAU = true ∧ commP D B2 = true ∧ commP D B3 = true ∧
    commP B2 B3 = true ∧ Nat.beq (pw D 3) pI = true ∧ Nat.beq (pw B2 3) pI = true ∧
    Nat.beq (pw B3 3) pI = true ∧ ntK D B2 B3 = true := by
  unfold relK at k
  obtain ⟨r1, k⟩ := band k
  obtain ⟨r2, k⟩ := band k
  obtain ⟨r3, k⟩ := band k
  obtain ⟨r4, k⟩ := band k
  obtain ⟨r5, k⟩ := band k
  obtain ⟨r6, k⟩ := band k
  obtain ⟨r7, k⟩ := band k
  obtain ⟨r8, k⟩ := band k
  obtain ⟨r9, k⟩ := band k
  obtain ⟨r10, k⟩ := band k
  obtain ⟨r11, r12⟩ := band k
  exact ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩

theorem ntK_spec {D B2 B3 : Nat} (k : ntK D B2 B3 = true) {t : Nat} (ht : t < 27) (h0 : t ≠ 0) :
    Nat.beq (pm (pw D (Nat.mod t 3)) (pm (pw B2 (Nat.mod (Nat.div t 3) 3)) (pw B3 (Nat.div t 9))))
      pI = false := by
  unfold ntK at k
  have e := allN_spec k t ht
  beta_reduce at e
  have hb : Nat.beq t 0 = false := by
    cases h : Nat.beq t 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) h0
  rw [hb] at e
  unfold CFSG.KC.LinRep.nB at e
  cases hq : Nat.beq (pm (pw D (Nat.mod t 3)) (pm (pw B2 (Nat.mod (Nat.div t 3) 3))
    (pw B3 (Nat.div t 9)))) pI
  · rfl
  · rw [hq] at e
    exact absurd e (by decide)

theorem hw : szOK 1782 11 = true := rfl

theorem pH : permB 1782 11 (SuzHS.F 0) = true := by
  have h := kPerm
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1

theorem pD : permB 1782 11 (SuzHS.F 1) = true := by
  have h := kPerm
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem pB2 : permB 1782 11 (SuzHS.F 2) = true := by
  have h := kPerm
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem pB3 : permB 1782 11 (SuzHS.F 3) = true := by
  have h := kPerm
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem pM : permB 1782 11 (SuzHS.F 4) = true := by
  have h := kPerm
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem pV : permB 1782 11 Suz2306.V = true := by
  have h := kPerm
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem pT : permB 1782 11 (SuzInvT1.F 0) = true := by
  have h := kPerm
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem pTAU : permB 1782 11 TAU = true := permB_pcomp hw pV pM

theorem pXA : permB 1782 11 XA = true := CertificateChecks.KernelSuzA17321.pX

theorem h_eq : sH () = unpack 1782 11 (SuzHS.F 0) := SuzH.suzArr_eq (k := 0) (by norm_num)

theorem d_eq : sD () = unpack 1782 11 (SuzHS.F 1) := SuzH.suzArr_eq (k := 1) (by norm_num)

theorem b2_eq : sB2 () = unpack 1782 11 (SuzHS.F 2) := SuzH.suzArr_eq (k := 2) (by norm_num)

theorem b3_eq : sB3 () = unpack 1782 11 (SuzHS.F 3) := SuzH.suzArr_eq (k := 3) (by norm_num)

theorem m_eq : sM () = unpack 1782 11 (SuzHS.F 4) := SuzH.suzArr_eq (k := 4) (by norm_num)

theorem t_eq : tTab = unpack 1782 11 (SuzInvT1.F 0) := CertificateChecks.KernelLC.B0Suz.t_eq

theorem xa_eq : xAArr (levels ()) = unpack 1782 11 XA := CertificateChecks.KernelSuzA17321.hX

theorem tau_eq : sTau () = unpack 1782 11 TAU := by
  unfold sTau
  rw [Suz2306.vArr_eq, m_eq, comp_unpack' hw pV pM]
  rfl

theorem inP_of {g : Array Nat} {G : Nat} (hg : g = unpack 1782 11 G) (hp : permB 1782 11 G = true)
    (hs : siftS G = true) : inP (levels ()) g = true := by
  have hc := (pp_of_permB hw hp).1
  have e := CertificateChecks.KernelSpor.OddCore.inM_eq hg hc
  change inM g = true
  rw [e]
  exact hs

theorem comm_eq {p q : Nat} (hp : permB 1782 11 p = true) (hq : permB 1782 11 q = true) :
    comm1782 (unpack 1782 11 p) (unpack 1782 11 q) = commP p q := by
  unfold comm1782
  rw [comp_unpack' hw hp hq, comp_unpack' hw hq hp,
    eqA_unpack' hw (permB_pcomp hw hp hq) (permB_pcomp hw hq hp)]
  rfl

theorem cube_eq {p : Nat} (hp : permB 1782 11 p = true) :
    eqA 1782 (powArr 1782 (unpack 1782 11 p) 3) (idA 1782) = Nat.beq (pw p 3) pI := by
  rw [pow_unpack' hw hp, idA_eq hw, eqA_unpack' hw (permB_ppow hw hp 3)
    (permB_of_pp (PP.id hw))]
  rfl

theorem conj_eq {h x : Nat} (hh : permB 1782 11 h = true) (hx : permB 1782 11 x = true)
    (d : Nat) (hd : permB 1782 11 d = true) :
    eqA 1782 (unpack 1782 11 d)
      (conj1782 (unpack 1782 11 h) (invCand 1782 (unpack 1782 11 h)) (unpack 1782 11 x)) =
      Nat.beq d (conjP h x) := by
  have hi := permB_pinvS hw hh
  unfold conj1782
  rw [invCand_PP (pp_of_permB hw hh), comp_unpack' hw hx hi, comp_unpack' hw hh (permB_pcomp hw hx hi),
    eqA_unpack' hw hd (permB_pcomp hw hh (permB_pcomp hw hx hi))]
  rfl

theorem prod3_eq {a b c : Nat} (ha : permB 1782 11 a = true) (hb : permB 1782 11 b = true)
    (hc : permB 1782 11 c = true) (e f g : Nat) :
    eqA 1782 (compA 1782 (powArr 1782 (unpack 1782 11 a) e)
      (compA 1782 (powArr 1782 (unpack 1782 11 b) f) (powArr 1782 (unpack 1782 11 c) g)))
      (idA 1782) = Nat.beq (pm (pw a e) (pm (pw b f) (pw c g))) pI := by
  have hb' := permB_ppow hw hb f
  have hc' := permB_ppow hw hc g
  have ha' := permB_ppow hw ha e
  rw [pow_unpack' hw ha, pow_unpack' hw hb, pow_unpack' hw hc, comp_unpack' hw hb' hc',
    comp_unpack' hw ha' (permB_pcomp hw hb' hc'), idA_eq hw,
    eqA_unpack' hw (permB_pcomp hw ha' (permB_pcomp hw hb' hc')) (permB_of_pp (PP.id hw))]
  rfl

theorem deg_facts :
    validA 1782 (sH ()) = true ∧ inP (levels ()) (sH ()) = true ∧ validA 1782 (sD ()) = true ∧
    validA 1782 (sB2 ()) = true ∧ validA 1782 (sB3 ()) = true ∧ validA 1782 (sM ()) = true ∧
    inP (levels ()) (sM ()) = true ∧ inP (levels ()) (sB2 ()) = true ∧
    inP (levels ()) (sB3 ()) = true ∧ validA 1782 (xAArr (levels ())) = true ∧
    eqA 1782 (sD ()) (conj1782 (sH ()) (invCand 1782 (sH ())) (xAArr (levels ()))) = true ∧
    comm1782 tTab (sD ()) = true ∧ comm1782 tTab (sB2 ()) = true ∧ comm1782 tTab (sB3 ()) = true ∧
    comm1782 tTab (sTau ()) = true ∧ comm1782 (sD ()) (sB2 ()) = true ∧
    comm1782 (sD ()) (sB3 ()) = true ∧ comm1782 (sB2 ()) (sB3 ()) = true ∧
    eqA 1782 (powArr 1782 (sD ()) 3) (idA 1782) = true ∧
    eqA 1782 (powArr 1782 (sB2 ()) 3) (idA 1782) = true ∧
    eqA 1782 (powArr 1782 (sB3 ()) 3) (idA 1782) = true ∧
    allBelow 27 (fun t => t == 0 || !(eqA 1782 (compA 1782 (powArr 1782 (sD ()) (t % 3))
      (compA 1782 (powArr 1782 (sB2 ()) (t / 3 % 3)) (powArr 1782 (sB3 ()) (t / 9)))) (idA 1782))) =
      true := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := relK_spec kRel
  rw [h_eq, d_eq, b2_eq, b3_eq, m_eq, xa_eq, t_eq, tau_eq]
  have va := fun {p : Nat} (hp : permB 1782 11 p = true) => CFSG.KC.Misc.ArrEnum.validA_unpack hp
  refine ⟨va pH, inP_of rfl pH kSiftH, va pD, va pB2, va pB3, va pM, inP_of rfl pM kSiftM,
    inP_of rfl pB2 kSiftB2, inP_of rfl pB3 kSiftB3, va pXA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [conj_eq pH pXA _ pD]
    exact r1
  · rw [comm_eq pT pD]
    exact r2
  · rw [comm_eq pT pB2]
    exact r3
  · rw [comm_eq pT pB3]
    exact r4
  · rw [comm_eq pT pTAU]
    exact r5
  · rw [comm_eq pD pB2]
    exact r6
  · rw [comm_eq pD pB3]
    exact r7
  · rw [comm_eq pB2 pB3]
    exact r8
  · rw [cube_eq pD]
    exact r9
  · rw [cube_eq pB2]
    exact r10
  · rw [cube_eq pB3]
    exact r11
  · simp only [allBelow, List.all_eq_true, List.mem_range]
    intro t ht
    rw [prod3_eq pD pB2 pB3]
    by_cases h0 : t = 0
    · subst h0
      rfl
    · have e : Nat.beq (pm (pw (SuzHS.F 1) (t % 3)) (pm (pw (SuzHS.F 2) (t / 3 % 3))
          (pw (SuzHS.F 3) (t / 9)))) pI = false := ntK_spec r12 ht h0
      rw [e]
      simp

end CertificateChecks.KernelSpor.SuzI301K

end
