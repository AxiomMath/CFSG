module

public import Certificates.Kernel.GLQ.HNTwo

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGLQ.HNTwo

open CFSG.KC.Ord CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.SectionRank.Native CFSG.Sporadic.GLQ
open CFSG.Sporadic.GLQ.HNTwoRank CFSG.KS.SporSch.LyM CFSG.Blueprint

@[expose] def Stmt : Prop :=
  ((opsP 5 133).eq ((opsP 5 133).pow ((opsP 5 133).decode NativeSporadic.HNSeed1) 2)
      (opsP 5 133).one = true) ∧
    ((opsP 5 133).eq ((opsP 5 133).pow ((opsP 5 133).decode NativeSporadic.HNSeed2) 3)
      (opsP 5 133).one = true) ∧
    (hnCheck = true)

theorem hn_gen {V' : Type} {O' : Ops Nat V'} (H : Hom (opsP 5 133) O') {A B : Nat}
    (hPA : H.P A) (hPB : H.P B)
    (hA : (opsP 5 133).decode NativeSporadic.HNSeed1 = H.U A)
    (hB : (opsP 5 133).decode NativeSporadic.HNSeed2 = H.U B)
    (h1 : O'.eq (O'.pow A 2) O'.one = true) (h2 : O'.eq (O'.pow B 3) O'.one = true)
    (hk : elem2OK O' (List.ofFn fun j =>
      signedWordN O' (runProgN O' (initRegsN O' 11 (A, A) (B, O'.pow B 2)) hnProg)[1]!
        (runProgN O' (initRegsN O' 11 (A, A) (B, O'.pow B 2)) hnProg)[2]! (hnWords j)) [0] = true) :
    Stmt := by
  obtain ⟨eA2, pA2⟩ := H.pow_U 2 hPA
  obtain ⟨eB3, pB3⟩ := H.pow_U 3 hPB
  obtain ⟨eB2, pB2⟩ := H.pow_U 2 hPB
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, eA2, H.one.1, H.eq pA2 H.one.2]
    exact h1
  · rw [hB, eB3, H.one.1, H.eq pB3 H.one.2]
    exact h2
  have hinit : initRegsN (opsP 5 133) 11 ((opsP 5 133).decode NativeSporadic.HNSeed1,
      (opsP 5 133).decode NativeSporadic.HNSeed1)
      ((opsP 5 133).decode NativeSporadic.HNSeed2,
        (opsP 5 133).pow ((opsP 5 133).decode NativeSporadic.HNSeed2) 2) =
      (initRegsN O' 11 (A, A) (B, O'.pow B 2)).map H.UU := by
    rw [hA, hB, eB2]
    exact H.initRegsN_U 11 (A, A) (B, O'.pow B 2)
  obtain ⟨hrun, hsize, hP⟩ := H.runProgN_U 11 hnProg kLt (initRegsN O' 11 (A, A) (B, O'.pow B 2))
    (by simp [initRegsN]) (H.initRegsN_P ⟨hPA, hPA⟩ ⟨hPB, pB2⟩)
  unfold hnCheck
  rw [kLt, Bool.true_and]
  unfold hnRegs
  rw [hinit, hrun]
  generalize runProgN O' (initRegsN O' 11 (A, A) (B, O'.pow B 2)) hnProg = R at hsize hP hk ⊢
  have p1 := hP 1 (by rw [hsize]; norm_num)
  have p2 := hP 2 (by rw [hsize]; norm_num)
  rw [get_map _ H.UU (by rw [hsize]; norm_num), get_map _ H.UU (by rw [hsize]; norm_num)]
  have hl : (List.ofFn fun j => signedWordN (opsP 5 133) (H.UU R[1]!) (H.UU R[2]!) (hnWords j)) =
      (List.ofFn fun j => signedWordN O' R[1]! R[2]! (hnWords j)).map H.U := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    exact (H.signedWordN_U p1 p2 (hnWords j)).1
  rw [hl, H.elem2OK_U ?_ [0]]
  · exact hk
  · intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact (H.signedWordN_U p1 p2 (hnWords j)).2

theorem hn_of {cs1 cs2 : List Char} (e1 : NativeSporadic.HNSeed1 = String.ofList cs1)
    (e2 : NativeSporadic.HNSeed2 = String.ofList cs2)
    (hk : forceB (pay cs1) (fun A => forceB (pay cs2) fun B => checkHN A B) = true) : Stmt := by
  rw [forceB_eq, forceB_eq] at hk
  generalize hpa : pay cs1 = A at hk
  generalize hpb : pay cs2 = B at hk
  unfold checkHN at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨hvA, hvB⟩, h1⟩, h2⟩, hk⟩ := hk
  rw [powN_eq _ _ _ _ (by norm_num)] at h1 h2
  rw [forceB_eq, powN_eq _ _ _ _ (by norm_num), runK_eq, forceL_eq] at hk
  have hdec : ∀ {cs : List Char} {X : Nat}, pay cs = X →
      (opsP 5 133).decode (String.ofList cs) = unpackL 133 13 1729 X := by
    intro cs X h
    rw [← h]
    exact payRunP_eqL cs (by norm_num) (by norm_num) (by norm_num)
  exact hn_gen (homP kConsts (by norm_num)) hvA hvB (by rw [e1]; exact hdec hpa)
    (by rw [e2]; exact hdec hpb) h1 h2 hk

theorem facts2081 : Stmt := hn_of HS1.eq HS2.eq kHN

end CertificateChecks.KernelGLQ.HNTwo

end
