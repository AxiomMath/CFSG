module

public import Certificates.Kernel.ONSeven.C8135
public import Certificates.Kernel.ONSeven.RDefs
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Spor.ONSevenRSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.ONR CFSG.KC.B3S3K CFSG.RankThree.Native
open CertificateChecks.KernelSpor.ONS (WW letOK letM_of lets_all getD_mem map_get arr_get)

theorem words_get {ws : Array (List Int)} (hl : ws.toList.all letOK = true) {s x : Nat}
    (hs : s < ws.size) (hx : x < 245520) :
    ((ws.map onSevenArr)[s]!)[x]! = WW (ws.getD s []) x := by
  rw [map_get ws hs]
  exact arr_get (letM_of (lets_all hl (getD_mem [] hs))) hx

theorem qWords_ok : qWords.toList.all letOK = true := by decide +kernel

theorem cWords_ok {r : Nat} (hr : r < 5) : (cWords r).toList.all letOK = true := by
  interval_cases r <;> decide +kernel

theorem qAll_eq : onSevenQArrs ++ onSevenLineArrs = qWords.map onSevenArr := by
  unfold onSevenQArrs onSevenLineArrs qWords
  rw [Array.map_append]

theorem cAll_eq {r : Nat} (hr : r < 5) :
    (onSevenCArrs r).push (onSevenRepArr r) ++ (if r < 3 then onSevenFArrs r else #[]) =
      (cWords r).map onSevenArr := by
  have h1 : onSevenCentWords[r]! = onSevenCentWords.getD r #[] :=
    (CertificateChecks.KernelSpor.ONS.getD_eq _ _ (by have : onSevenCentWords.size = 5 := rfl; omega)).symm
  have h2 : onSevenRepArr r = onSevenArr (onSevenLineWords.getD (onSevenRepIdx.getD r 0) []) := by
    unfold onSevenRepArr onSevenLineArrs
    have hi := CertificateChecks.KernelSpor.ONS.repIdx_lt hr
    rw [← CertificateChecks.KernelSpor.ONS.getD_eq onSevenRepIdx 0
      (by have : onSevenRepIdx.size = 5 := rfl; omega)]
    exact map_get _ (by have : onSevenLineWords.size = 57 := rfl; omega)
  unfold onSevenCArrs cWords
  rw [h1, h2, ← Array.map_push, Array.map_append]
  congr 1
  by_cases h3 : r < 3
  · simp only [h3, ↓reduceIte, onSevenFArrs]
    rw [CertificateChecks.KernelSpor.ONS.getD_eq _ _ (by have : onSevenNormalWords.size = 3 := rfl; omega)]
  · simp [h3]

theorem prefix_get {gs rest : Array (Array Nat)} {F : Nat → Nat → Nat}
    (h : ∀ s < (gs ++ rest).size, ∀ x < 245520, ((gs ++ rest)[s]!)[x]! = F s x) :
    ∀ s < gs.size, ∀ x < 245520, (gs[s]!)[x]! = F s x := by
  intro s hs x hx
  have := h s (by simp; omega) x hx
  rwa [getElem!_pos (gs ++ rest) s (by simp; omega), Array.getElem_append_left hs,
    ← getElem!_pos gs s hs] at this

theorem suffix_get {gs rest : Array (Array Nat)} {F : Nat → Nat → Nat}
    (h : ∀ s < (gs ++ rest).size, ∀ x < 245520, ((gs ++ rest)[s]!)[x]! = F s x) :
    ∀ s < rest.size, ∀ x < 245520, (rest[s]!)[x]! = F (gs.size + s) x := by
  intro s hs x hx
  have := h (gs.size + s) (by simp; omega) x hx
  have e : (gs ++ rest)[gs.size + s]! = rest[s]! := by
    rw [getElem!_pos _ _ (by simp; omega), getElem!_pos rest s hs]
    simp [Array.getElem_append_right]
  rwa [e] at this

theorem push_get {gs : Array (Array Nat)} {x : Array Nat} {F : Nat → Nat → Nat}
    (h : ∀ s < (gs.push x).size, ∀ y < 245520, ((gs.push x)[s]!)[y]! = F s y) :
    (∀ s < gs.size, ∀ y < 245520, (gs[s]!)[y]! = F s y) ∧ ∀ y < 245520, x[y]! = F gs.size y := by
  rw [← Array.append_singleton] at h
  refine ⟨prefix_get h, fun y hy => ?_⟩
  have := suffix_get h 0 (by simp) y hy
  simpa using this

theorem bind_of {N w k : Nat} {T G D S : Nat → Nat} {gs : Array (Array Nat)} {F : Nat → Nat → Nat}
    {GR : Nat → Nat} (ho : orbK N w k T G D S = true)
    (hF : ∀ s < gs.size, ∀ x < 245520, (gs[s]!)[x]! = F s x)
    (hr : ∀ s < gs.size, resK N w T (F s) (GR s) = true) :
    BindA N w (gs.map (onSevenTab (Array.ofFn (n := N) fun i => T i.val))) gs.size GR := by
  have O := orbK_spec ho
  refine ⟨by simp, fun s hs => ?_⟩
  rw [getElem!_pos _ s (by simpa using hs), Array.getElem_map, ← getElem!_pos gs s hs]
  exact tab_eq (hF s hs) O.lt O.inj (hr s hs)

end CertificateChecks.KernelSpor.ONR

end
