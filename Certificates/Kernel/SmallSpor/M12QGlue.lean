module

public import Certificates.Data.ExitTwoM12
import Certificates.Kernel.SmallSpor.M12QChecks
import Certificates.Kernel.SmallSpor.M12Checks
import Certificates.Kernel.SporSch.Mathieu.M12Facts
import CFSG.Certificates.Kernel.ListBridge.TwinSound
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.ClassicalInvolution.SmallCases.Sporadic.M12Inputs

namespace CertificateChecks.KernelSmallSpor.M12Q

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ClassicalInvolution
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KC.ListBridge
open CFSG.ClassicalInvolution.ListBridge CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12
open CFSG.ClassicalInvolution.Q3.TL4.MF163 CFSG.KS.SporSch.MOC
open CertificateChecks.KernelSmallSpor.M12 CertificateChecks.KernelSporSch
open CFSG.KLie.CT (notB)
open CFSG.KC.BfsPin (bfsK_canon allN_intro)

theorem notB_eq {b : Bool} (h : notB b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem bIf_or {c t : Bool} (h : Bool.rec (motive := fun _ => Bool) t true c = true) :
    c = true ∨ t = true := by
  cases c
  · exact Or.inr h
  · exact Or.inl rfl

theorem k1_eq : m12KGens1 = m12CentWords1.map (evalCodes [m12gA, m12gB]) := by
  simp only [m12KGens1, tabWords, tab_eq]

theorem lenK1 : m12KGens1.length = EK1.ng := by
  rw [Nat.eq_of_beq_eq_true nums.1, k1_eq, List.length_map]
  rfl

theorem prepK1 : ∀ j < EK1.ng, PRep 12 4 (EK1.G j) (m12KGens1.getD j 1) := by
  intro j hj
  rw [Nat.eq_of_beq_eq_true (allN_spec bindK1 j (by rwa [← Nat.eq_of_beq_eq_true nums.1]))]
  rw [k1_eq]
  have hj' : j < (m12CentWords1.map (evalCodes [m12gA, m12gB])).length := by
    rw [← k1_eq, lenK1]
    exact hj
  exact prep_of_imageList (M12OC.chainC1.2.2.2.1 j hj')

theorem memK (g : Equiv.Perm (Fin 12)) :
    g ∈ enumerationTab m12CentQ1 ↔ ∃ i < EK1.N, PRep 12 4 (EK1.T i) g := by
  rw [mem_enumerationTab_iff m12CentQ1 M12OC.cent1.1, m12CentQ1, certificate_originalSubgroup,
    ← k1_eq]
  exact (enum_closure EK1.ok lenK1 prepK1).1 g

theorem crK {i : Nat} {g : Equiv.Perm (Fin 12)} (hi : i < EK1.N) (hp : PRep 12 4 (EK1.T i) g) :
    CR 12 4 (EK1.T i) g := ⟨bfsK_canon EK1.ok i hi, hp⟩

theorem imgBp : imageList m12bp = (unpack 12 4 (WV 0)).toList := by
  rw [← tBp_eq, ← toArray_eq_of_bindListK bindBp.1]

theorem wordA {wd : List Int} (hw : abOK wd = true) :
    PRep 12 4 (wA wd) (evalCodes [m12gA, m12gB] wd) :=
  prep_of_imageList (abWordK_rep' M12OC.szOK' M12OC.imgA M12OC.imgB M12OC.pA M12OC.pB hw)

theorem wordB {wd : List Int} (hw : abOK wd = true) :
    PRep 12 4 (wB wd) (evalCodes [m12gA, m12bp] wd) :=
  prep_of_imageList (abWordK_rep' M12OC.szOK' M12OC.imgA imgBp M12OC.pA bindBp.2 hw)

theorem eqB {P Q : Nat} (h : Nat.beq P Q = true) : P = Q := Nat.eq_of_beq_eq_true h

theorem shape_of {Q : Nat → Nat} (h : q8K Q = true) :
    Q 0 = pidn 12 4 ∧ Q 2 = pcomp 12 4 (mask 4) (Q 1) (Q 1) ∧
      Q 3 = pcomp 12 4 (mask 4) (Q 2) (Q 1) ∧ Q 5 = pcomp 12 4 (mask 4) (Q 1) (Q 4) ∧
      Q 6 = pcomp 12 4 (mask 4) (Q 2) (Q 4) ∧ Q 7 = pcomp 12 4 (mask 4) (Q 3) (Q 4) := by
  unfold q8K at h
  obtain ⟨h0, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h5, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h6, h7⟩ := (bAnd_iff _ _).1 h
  exact ⟨eqB h0, eqB h2, eqB h3, eqB h5, eqB h6, eqB h7⟩

theorem twin_of {Q : Nat → Nat} {i j : Equiv.Perm (Fin 12)} (hs : q8K Q = true)
    (hc : allN 8 (fun k => canonK 12 4 (mask 4) (12 * 4) (Q k)) = true)
    (hI : PRep 12 4 (Q 1) i) (hJ : PRep 12 4 (Q 4) j) :
    TwinSet 12 4 (q8List i j) 8 Q ∧ PRep 12 4 (Q 2) (i * i) ∧ PRep 12 4 (Q 6) (i * i * j) ∧
      PRep 12 4 (Q 7) (i * i * i * j) := by
  obtain ⟨h0, h2, h3, h5, h6, h7⟩ := shape_of hs
  exact q8_twin M12OC.szOK' (allN_spec hc) hI hJ h0 h2 h3 h5 h6 h7

theorem prepQ0 : PRep 12 4 (Q0 1) (evalCodes [m12gA, m12gB] wI0) ∧
    PRep 12 4 (Q0 4) (evalCodes [m12gA, m12gB] wJ0) := by
  rw [eqB binds.1, eqB binds.2.1]
  exact ⟨wordA words.1, wordA words.2.1⟩

theorem prepQ1 : PRep 12 4 (Q1 1) (evalCodes [m12gA, m12gB] wI1) ∧
    PRep 12 4 (Q1 4) (evalCodes [m12gA, m12gB] wJ1) := by
  rw [eqB binds.2.2.1, eqB binds.2.2.2.1]
  exact ⟨wordA words.2.2.1, wordA words.2.2.2.1⟩

theorem prepB0 : PRep 12 4 (B0 1) (evalCodes [m12gA, m12bp] wI0) ∧
    PRep 12 4 (B0 4) (evalCodes [m12gA, m12bp] wJ0) := by
  rw [eqB binds.2.2.2.2.1, eqB binds.2.2.2.2.2.1]
  exact ⟨wordB words.1, wordB words.2.1⟩

theorem prepB1 : PRep 12 4 (B1 1) (evalCodes [m12gA, m12bp] wI1) ∧
    PRep 12 4 (B1 4) (evalCodes [m12gA, m12bp] wJ1) := by
  rw [eqB binds.2.2.2.2.2.2.1, eqB binds.2.2.2.2.2.2.2.1]
  exact ⟨wordB words.2.2.1, wordB words.2.2.2.1⟩

@[reducible] def TW (S : List (Equiv.Perm (Fin 12))) (Q : Nat → Nat) (wi wj : List Int) : Prop :=
  TwinSet 12 4 (q8List (evalCodes S wi) (evalCodes S wj)) 8 Q ∧
    PRep 12 4 (Q 2) (evalCodes S wi * evalCodes S wi) ∧
    PRep 12 4 (Q 6) (evalCodes S wi * evalCodes S wi * evalCodes S wj) ∧
    PRep 12 4 (Q 7) (evalCodes S wi * evalCodes S wi * evalCodes S wi * evalCodes S wj)

theorem T0 : TW [m12gA, m12gB] Q0 wI0 wJ0 := twin_of shape.1 canon.1 prepQ0.1 prepQ0.2

theorem T1 : TW [m12gA, m12gB] Q1 wI1 wJ1 := twin_of shape.2.1 canon.2.1 prepQ1.1 prepQ1.2

theorem TB0 : TW [m12gA, m12bp] B0 wI0 wJ0 := twin_of shape.2.2.1 canon.2.2.1 prepB0.1 prepB0.2

theorem TB1 : TW [m12gA, m12bp] B1 wI1 wJ1 :=
  twin_of shape.2.2.2 canon.2.2.2.1 prepB1.1 prepB1.2

theorem L0 : TwinSet 12 4 (quatL0 ()) 8 Q0 := T0.1

theorem L1 : TwinSet 12 4 (quatL1 ()) 8 Q1 := T1.1

theorem LB0 : TwinSet 12 4 (betaL0 ()) 8 B0 := TB0.1

theorem LB1 : TwinSet 12 4 (betaL1 ()) 8 B1 := TB1.1

theorem crR : CR 12 4 M12OC.R0 m12Rep1 := ⟨canon.2.2.2.2.1, prep_of_imageList M12OC.imgRep0⟩

theorem crG : CR 12 4 (WV 2) (evalCodes [m12gA, m12gB] wG) := by
  refine ⟨canon.2.2.2.2.2, ?_⟩
  rw [eqB binds.2.2.2.2.2.2.2.2]
  exact wordA words.2.2.2.2

theorem crOne : CR 12 4 (pidn 12 4) 1 := CR.one M12OC.szOK'

theorem c1 : chkMemC () = true := by
  unfold chkMemC
  rw [List.all_eq_true]
  intro x hx
  rw [decide_eq_true_eq, memK]
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨k, hk, hc⟩ := L0.cr hx
    exact prep_of_inK (allN_spec memC.1 k hk) hc.2
  · obtain ⟨k, hk, hc⟩ := L1.cr hx
    exact prep_of_inK (allN_spec memC.2 k hk) hc.2

theorem c2 : chkClosed () = true := by
  unfold chkClosed
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨fun a ha b hb => ?_, fun a ha b hb => ?_⟩, fun a ha => ?_⟩, fun a ha => ?_⟩
  · obtain ⟨k, hk, hck⟩ := L0.cr ha
    obtain ⟨l, hl, hcl⟩ := L0.cr hb
    exact (L0.mem_iff (hck.mul hcl)).2 (allN_spec (allN_spec closed.1 k hk) l hl)
  · obtain ⟨k, hk, hck⟩ := L1.cr ha
    obtain ⟨l, hl, hcl⟩ := L1.cr hb
    exact (L1.mem_iff (hck.mul hcl)).2 (allN_spec (allN_spec closed.2.1 k hk) l hl)
  · obtain ⟨k, hk, hck⟩ := L0.cr ha
    exact (L0.mem_iff hck.inv).2 (allN_spec closed.2.2.1 k hk)
  · obtain ⟨k, hk, hck⟩ := L1.cr ha
    exact (L1.mem_iff hck.inv).2 (allN_spec closed.2.2.2 k hk)

theorem root_cr {x : Equiv.Perm (Fin 12)} (hx : x ∈ m12SqRoots1) :
    ∃ k < NR 0, CR 12 4 (EK1.T (RI k)) x := by
  rw [m12SqRoots1, List.mem_filter, decide_eq_true_eq, memK] at hx
  obtain ⟨⟨i, hi, hp⟩, hsq⟩ := hx
  have hc := crK hi hp
  have hb : Nat.beq (pcomp 12 4 (mask 4) (EK1.T i) (EK1.T i)) M12OC.R0 = true :=
    ((hc.mul hc).beq_iff crR).1 hsq
  have h := allN_spec rootsAll i hi
  rw [hb] at h
  obtain ⟨k, hk, e⟩ := inK_spec h
  exact ⟨k, hk, by rw [e]; exact hc⟩

theorem c3 : chkRoots () = true := by
  unfold chkRoots
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  intro x hx
  obtain ⟨k, hk, hck⟩ := root_cr hx
  have h := allN_spec rootsPair k hk
  rw [Orb.strictB_eq] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hA : x ∈ quatL0 () ∨ x ∈ quatL1 () := by
    rcases bIf_or h1 with h | h
    · exact Or.inl ((L0.mem_iff hck).2 h)
    · exact Or.inr ((L1.mem_iff hck).2 h)
  refine ⟨hA, fun y hy => ?_⟩
  obtain ⟨l, hl, hcl⟩ := root_cr hy
  have h3 := allN_spec h2 l hl
  rw [Orb.strictB_eq] at h3
  rcases bIf_or h3 with h | h
  · have : x * y = y * x := ((hck.mul hcl).beq_iff (hcl.mul hck)).2 h
    first
      | exact Or.inl (Or.inl this)
      | exact Or.inl this
  · rcases bIf_or h with h | h
    · obtain ⟨ha, hb⟩ := (bAnd_iff _ _).1 h
      have : x ∈ quatL0 () ∧ y ∈ quatL0 () := ⟨(L0.mem_iff hck).2 ha, (L0.mem_iff hcl).2 hb⟩
      first
        | exact Or.inl (Or.inr this)
        | exact Or.inr (Or.inl this)
    · obtain ⟨ha, hb⟩ := (bAnd_iff _ _).1 h
      have : x ∈ quatL1 () ∧ y ∈ quatL1 () := ⟨(L1.mem_iff hck).2 ha, (L1.mem_iff hcl).2 hb⟩
      first
        | exact Or.inr this
        | exact Or.inr (Or.inr this)

theorem c4 : chkNorm () = true := by
  unfold chkNorm
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  intro g hg
  obtain ⟨i, hi, hp⟩ := (memK g).1 hg
  have hc := crK hi hp
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨k, hk, hck⟩ := L0.cr ha
    exact (L0.mem_iff ((hc.mul hck).mul hc.inv)).2
      ((bAnd_iff _ _).1 (allN_spec (allN_spec norm i hi) k hk)).1
  · obtain ⟨k, hk, hck⟩ := L1.cr ha
    exact (L1.mem_iff ((hc.mul hck).mul hc.inv)).2
      ((bAnd_iff _ _).1 (allN_spec (allN_spec norm i hi) k hk)).2

theorem c5 : chkBeta () = true := by
  unfold chkBeta
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨k, hk, hck⟩ := LB0.cr hx
    exact (L1.mem_iff hck).2 (allN_spec beta.1 k hk)
  · obtain ⟨k, hk, hck⟩ := LB1.cr hx
    exact (L0.mem_iff hck).2 (allN_spec beta.2 k hk)

theorem crU : CR 12 4 (cj (WV 2) (Q1 7)) (witU ()) := by
  have e : witU () = evalCodes [m12gA, m12gB] wG *
      (evalCodes [m12gA, m12gB] wI1 * evalCodes [m12gA, m12gB] wI1 *
        evalCodes [m12gA, m12gB] wI1 * evalCodes [m12gA, m12gB] wJ1) *
      (evalCodes [m12gA, m12gB] wG)⁻¹ := rfl
  rw [e]
  have h7 : CR 12 4 (Q1 7) (evalCodes [m12gA, m12gB] wI1 * evalCodes [m12gA, m12gB] wI1 *
      evalCodes [m12gA, m12gB] wI1 * evalCodes [m12gA, m12gB] wJ1) :=
    ⟨allN_spec canon.2.1 7 (by norm_num), T1.2.2.2⟩
  exact (crG.mul h7).mul crG.inv

theorem crV : CR 12 4 (cj (WV 2) (Q1 6)) (witV ()) := by
  have e : witV () = evalCodes [m12gA, m12gB] wG *
      (evalCodes [m12gA, m12gB] wI1 * evalCodes [m12gA, m12gB] wI1 *
        evalCodes [m12gA, m12gB] wJ1) * (evalCodes [m12gA, m12gB] wG)⁻¹ := rfl
  rw [e]
  have h6 : CR 12 4 (Q1 6) (evalCodes [m12gA, m12gB] wI1 * evalCodes [m12gA, m12gB] wI1 *
      evalCodes [m12gA, m12gB] wJ1) :=
    ⟨allN_spec canon.2.1 6 (by norm_num), T1.2.2.1⟩
  exact (crG.mul h6).mul crG.inv

theorem c6 : chkWit () = true := by
  unfold chkWit
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true,
    decide_eq_true_eq]
  obtain ⟨w1, w2, w3, w4⟩ := wit
  refine ⟨⟨⟨fun e => ?_, fun e => ?_⟩, fun a ha => ?_⟩, ?_⟩
  · have := (crU.beq_iff crOne).1 e
    rw [notB_eq w1] at this
    exact Bool.noConfusion this
  · have := ((crU.mul crU).beq_iff crOne).1 e
    rw [notB_eq w2] at this
    exact Bool.noConfusion this
  · obtain ⟨k, hk, hck⟩ := L0.cr ha
    exact (L0.mem_iff ((crU.mul hck).mul crU.inv)).2 (allN_spec w3 k hk)
  · rw [Bool.eq_false_iff]
    intro hall
    have h4 := notB_eq w4
    have hall' : allN 8 (fun a => inK 8 Q0 (cj (cj (WV 2) (Q1 6)) (Q0 a))) = true := by
      refine allN_intro fun k hk => ?_
      obtain ⟨x, hx, hcx⟩ := L0.exists_cr hk
      have := of_decide_eq_true (List.all_eq_true.1 hall x hx)
      exact (L0.mem_iff ((crV.mul hcx).mul crV.inv)).1 this
    rw [h4] at hall'
    exact Bool.noConfusion hall'

theorem c7 : chkMeet () = true := by
  unfold chkMeet
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true, decide_eq_true_eq]
  obtain ⟨m1, m2, m3⟩ := meet
  have e0 : (quatL0 ()).getD 2 1 = evalCodes [m12gA, m12gB] wI0 * evalCodes [m12gA, m12gB] wI0 :=
    rfl
  have e1 : (quatL1 ()).getD 2 1 = evalCodes [m12gA, m12gB] wI1 * evalCodes [m12gA, m12gB] wI1 :=
    rfl
  have g0 : (quatL0 ()).getD 2 1 = m12Rep1 := by
    rw [e0]
    have h2 : CR 12 4 (Q0 2) (evalCodes [m12gA, m12gB] wI0 * evalCodes [m12gA, m12gB] wI0) :=
      ⟨allN_spec canon.1 2 (by norm_num), T0.2.1⟩
    exact (CR.beq_iff h2 crR).2 m2
  have g1 : (quatL1 ()).getD 2 1 = m12Rep1 := by
    rw [e1]
    have h2 : CR 12 4 (Q1 2) (evalCodes [m12gA, m12gB] wI1 * evalCodes [m12gA, m12gB] wI1) :=
      ⟨allN_spec canon.2.1 2 (by norm_num), T1.2.1⟩
    exact (CR.beq_iff h2 crR).2 m3
  refine ⟨⟨fun a ha => ?_, g0⟩, g1⟩
  obtain ⟨k, hk, hck⟩ := L0.cr ha
  have h := allN_spec m1 k hk
  cases hin : inK 8 Q1 (Q0 k)
  · have : a ∉ quatL1 () := fun h' => by
      rw [(L1.mem_iff hck).1 h'] at hin
      exact Bool.noConfusion hin
    first
      | exact Or.inl (Or.inl this)
      | exact Or.inl this
  · rw [hin] at h
    have h' : Bool.rec (motive := fun _ => Bool) (Nat.beq (Q0 k) M12OC.R0) true
        (Nat.beq (Q0 k) (pidn 12 4)) = true := h
    rcases bIf_or h' with h | h
    · have : a = 1 := (hck.beq_iff crOne).2 h
      first
        | exact Or.inl (Or.inr this)
        | exact Or.inr (Or.inl this)
    · have : a = m12Rep1 := (hck.beq_iff crR).2 h
      first
        | exact Or.inr this
        | exact Or.inr (Or.inr this)

public theorem check55112 : chkMemC () = true ∧ chkClosed () = true ∧ chkRoots () = true ∧
    chkNorm () = true ∧ chkBeta () = true ∧ chkWit () = true ∧ chkMeet () = true :=
  ⟨c1, c2, c3, c4, c5, c6, c7⟩

end CertificateChecks.KernelSmallSpor.M12Q
