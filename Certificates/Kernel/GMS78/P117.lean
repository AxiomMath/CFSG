module

public import Certificates.Kernel.GMS78.P117Tabs
public import Certificates.Kernel.GMS78.PChk
public import CFSG.Certificates.Kernel.GMS78RuPSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.SD

open CFSG.KC.GMS CFSG.KLie.CT CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS
  CFSG.GMS78RuSP

theorem ctAllN_spec {n : Nat} {f : Nat → Bool} (h : allN n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have h' : andB (f n) (allN n f) = true := h
    have e : ∀ a b : Bool, andB a b = true → a = true ∧ b = true := by
      intro a b; cases a <;> cases b <;> simp [andB]
    obtain ⟨h1, h2⟩ := e _ _ h'
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h2 i hi
    · exact h1

theorem neGet_eq {α : Type} (d : α) : ∀ (l : List α) (i : Nat), neGet d l i = l.getD i d
  | [], _ => rfl
  | a :: l, 0 => rfl
  | a :: l, i + 1 => by
    change neGet d l i = _
    rw [neGet_eq d l i]
    rfl

theorem gamArr_getD {i : Nat} (hi : i < 65536) : gamArr.getD i 0 = gam (i / 256) (i % 256) := by
  rw [gamArr, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range,
    ite_eq_left hi]
  rfl

theorem dPartArr_getD {i : Nat} (hi : i < 2048) :
    dPartArr.getD i (0, 0) = dPart (fin8Of (i / 256)) (i % 256) := by
  rw [dPartArr, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range,
    ite_eq_left hi]
  rfl

theorem beq_true {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem sTabs_true : sTabs gamArr dPartArr dCodeTab true GT DPR LIN DM DO1 := by
  have hg := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) gamB.all
  have hd := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) dpB.all
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun d hd8 t ht => ?_, fun d hd8 e he => ?_,
    fun d hd8 e he => ?_, fun i hi => ?_⟩
  · rw [gamArr_getD hi]
    have hc : i / 256 < 256 := (Nat.div_lt_iff_lt_mul (by norm_num)).2 (by norm_num; omega)
    exact beq_true (ctAllN_spec (hg (i / 256) hc) (i % 256) (Nat.mod_lt _ (by norm_num)))
  · have h := andB_true (hd i hi)
    have h2 := andB_true h.2
    rw [dPartArr_getD hi]
    exact ⟨beq_true h.1, beq_true h2.1⟩
  · have h := beq_true (ctAllN_spec linOK (8 * d + t) (by omega))
    have e1 : (8 * d + t) / 8 = d := by omega
    have e2 : (8 * d + t) % 8 = t := by omega
    rw [e1, e2] at h
    exact h
  · have h := beq_true (ctAllN_spec dmOK (8 * d + e) (by omega))
    have e1 : (8 * d + e) / 8 = d := by omega
    have e2 : (8 * d + e) % 8 = e := by omega
    rw [e1, e2] at h
    exact h
  · have h := ctAllN_spec do1OK (8 * d + e) (by omega)
    have e1 : (8 * d + e) / 8 = d := by omega
    have e2 : (8 * d + e) % 8 = e := by omega
    rw [e1, e2, beq_iff_eq] at h
    simpa using h
  · have h := andB_true (hd i hi)
    have h2 := andB_true h.2
    rw [dPartArr_getD hi]
    have h3 := h2.2
    rw [Nat.blt_eq] at h3
    exact h3

theorem czListEq_eq : ∀ {a b : List Nat}, czListEq a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [czListEq] at h
  | _ :: _, [], h => by simp [czListEq] at h
  | x :: a, y :: b, h => by
    have h' : andB (Nat.beq x y) (czListEq a b) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    rw [beq_true h1, czListEq_eq h2]

theorem len_CXL : CXL.length = 240 := by rfl
theorem len_F1L : F1L.length = 256 := by rfl
theorem len_KL : KL.length = 16 := by rfl

theorem jMem_gen : jMem = Gen.jMemG gamArr dPartArr dCodeTab xPts := by
  funext p
  rw [jMem, jArr, Gen.jMemG, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_range]
  by_cases h : encPt p < 16384
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]
    rfl

theorem checks15117 : checkA = true ∧ checkCa = true ∧ checkCx = true ∧ checkF1 = true ∧
    checkF3 = true ∧ checkJd = true := by
  have h := check15117_sound gamArr dPartArr dCodeTab xPts GT DPR LIN DM DO1 JM XS CXL F1L KL
    sTabs_true (czListEq_eq tX) tXs
    (CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) jmB.all) tA tL
    (fun i hi => by
      rw [len_CXL] at hi
      have := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) cxB.all i hi
      rwa [cxF, neGet_eq] at this)
    (fun i hi => by
      rw [len_F1L] at hi
      have := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) f1B.all i hi
      rwa [f1F, neGet_eq] at this)
    (fun i hi => by
      rw [len_KL] at hi
      have := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) f3B.all i hi
      rwa [f3F, neGet_eq] at this)
  have eF1 : checkF1 = Gen.checkF1G gamArr dPartArr dCodeTab xPts := by
    rw [checkF1, jMem_gen]
    rfl
  have eF3 : checkF3 = Gen.checkF3G gamArr dPartArr dCodeTab xPts := by
    rw [checkF3, jMem_gen]
    rfl
  rw [eF1, eF3]
  exact h

end CertificateChecks.KernelGMS78.SD

end
