module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCentralizerData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCentralizerData
public import Certificates.Kernel.J4M2.Base
public import Certificates.Kernel.J4M2.CommLo
public import Certificates.Kernel.J4M2.CommHi
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4M2 CertificateChecks.KernelJ4Q CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck

theorem cK_chk : Nat.beq cmK cK = true := by quickRfl

theorem cMat_encK : WfA cMat ∧ encR cMat = cK :=
  ⟨cMat_enc.1, cMat_enc.2.trans (Nat.eq_of_beq_eq_true cK_chk)⟩

@[expose] noncomputable def iterK (i x : Nat) : Nat := (List.range i).foldl (fun acc _ => mulJ c rm acc cK) x

theorem qProdK_eq (m : Nat) (e : Bool) : qProdK m e = if e then mulJ c rm (pK m) ZM else pK m := rfl

theorem kRows_enc (f : Bool × Nat × Nat) : WfA (kRows f) ∧
    encR (kRows f) = iterK f.2.2 (if f.1 then mulJ c rm (pK f.2.1) ZM else pK f.2.1) := by
  have key : ∀ (l : List Nat) (acc : Array V2) (a : Nat), WfA acc ∧ encR acc = a →
      WfA (l.foldl (fun acc _ => mulT acc cTab) acc) ∧
        encR (l.foldl (fun acc _ => mulT acc cTab) acc) = l.foldl (fun acc _ => mulJ c rm acc cK) a := by
    intro l
    induction l with
    | nil => intro acc a h; exact h
    | cons j l ih =>
      intro acc a h
      rw [List.foldl_cons, List.foldl_cons]
      apply ih
      rw [cTab, mulT_frTable]
      exact mul_enc hK h cMat_encK
  unfold kRows iterK
  rw [← qProdK_eq]
  exact key _ _ _ (qProd_enc _ _)

theorem kTab_get {n : Nat} (hn : n < 24576) : kTab[n]! = kRows (decodeF n) :=
  get!_range_map (fun n => kRows (decodeF n)) hn

theorem commC_all {m : Nat} (hm : m < 4096) : commC m = true := by
  have hk : m / 128 < 32 := by omega
  have e : 128 * (m / 128) + m % 128 = m := Nat.div_add_mod m 128
  by_cases hlo : m / 128 < 16
  · have h := allR_spec (CL.all (m / 128) hlo) (m % 128) (Nat.mod_lt _ (by omega))
    rwa [e] at h
  · have hlt : m / 128 - 16 < 16 := by omega
    have h0 := CH.all (m / 128 - 16) hlt
    have e2 : commBlkHi (m / 128 - 16) = commBlk (m / 128) :=
      congrArg commBlk (Nat.add_sub_cancel' (by omega))
    have h : commBlk (m / 128) = true := e2 ▸ h0
    have h2 := allR_spec h (m % 128) (Nat.mod_lt _ (by omega))
    rwa [e] at h2

theorem orB_false (b : Bool) : orB false b = b := rfl

theorem triK_spec {b : Nat} (h : triK b = true) : ∀ i < 3,
    Nat.beq (mulJ c rm (iterK i b) cK) (mulJ c rm cK (iterK i b)) = false := by
  unfold triK at h
  rw [strictB_eq, strictB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true,
    notB_eq, notB_eq, notB_eq, Bool.not_eq_true', Bool.not_eq_true', Bool.not_eq_true'] at h
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem comm_ok : chkComm = true := by
  unfold chkComm
  rw [Bool.and_eq_true]
  refine ⟨by simp [kTab], ?_⟩
  rw [List.all_eq_true]
  intro n hn
  have hn' := List.mem_range.1 hn
  dsimp only
  rw [kTab_get hn']
  have hm : (decodeF n).2.1 < 4096 := by simp only [decodeF]; omega
  have hi : (decodeF n).2.2 < 3 := by simp only [decodeF]; omega
  generalize decodeF n = f at hm hi ⊢
  obtain ⟨e, m, i⟩ := f
  simp only at hm hi ⊢
  have hX := kRows_enc (e, m, i)
  have hR : WfA (rightC (kRows (e, m, i))) ∧ encR (rightC (kRows (e, m, i))) =
      mulJ c rm (encR (kRows (e, m, i))) cK := by
    unfold rightC
    rw [cTab, mulT_frTable]
    exact mul_enc hK ⟨hX.1, rfl⟩ cMat_encK
  have hL : WfA (leftC (kRows (e, m, i))) ∧ encR (leftC (kRows (e, m, i))) =
      mulJ c rm cK (encR (kRows (e, m, i))) := by
    unfold leftC
    rw [mulT_frTable]
    exact mul_enc hK cMat_encK ⟨hX.1, rfl⟩
  have w1 : wfR (kRows (e, m, i)) = true := wf_bool hX.1
  have w2 : wfR (rightC (kRows (e, m, i))) = true := wf_bool hR.1
  have w3 : wfR (leftC (kRows (e, m, i))) = true := wf_bool hL.1
  rw [w1, w2, w3, eqRows_of hR hL, hX.2]
  by_cases h0 : m = 0
  · simp [h0]
  · have hc := commC_all hm
    unfold commC at hc
    have hb : Nat.beq m 0 = false := by
      cases hm' : Nat.beq m 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hm') h0
    rw [hb, orB_false, strictB_eq, andB_eq, Bool.and_eq_true] at hc
    have key : Nat.beq (mulJ c rm (iterK i (if e then mulJ c rm (pK m) ZM else pK m)) cK)
        (mulJ c rm cK (iterK i (if e then mulJ c rm (pK m) ZM else pK m))) = false := by
      cases e
      · exact triK_spec hc.1 i hi
      · exact triK_spec hc.2 i hi
    simp only [key]
    rfl

open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck in
theorem c12633 : chkComm = true := comm_ok

end CertificateChecks.KernelJ4M2

end
