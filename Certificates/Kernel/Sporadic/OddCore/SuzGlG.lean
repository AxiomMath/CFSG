module

public import Certificates.Kernel.Sporadic.OddCore.SuzGlF
public import Certificates.Kernel.Sporadic.ON.Gen
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kon_slices CertificateChecks.KernelSpor.SuzGl.y0Sl 0 4
#kon_slices CertificateChecks.KernelSpor.SuzGl.cASl 0 4
#kon_slices CertificateChecks.KernelSpor.SuzGl.nASl 0 8

namespace CertificateChecks.KernelSpor.SuzGl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Sporadic.SuzRecog.B0Gluing CFSG.Sporadic.SuzRecog.B0GluingData
open CFSG.Sporadic.SuzRecog.C1Model CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzTwCF
  CertificateChecks.KernelSpor.SuzMGF CertificateChecks.KernelSpor.SuzC1BF
  CertificateChecks.KernelSpor.SuzC1EG CertificateChecks.KernelSpor.SuzC1EF
  CertificateChecks.KernelSpor.SuzC1EV

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pgk" => pg 11 (mask 11)
local notation "g7" => pg 7 (mask 7)
local notation "T" => SuzC1ET.T

theorem y0OK_of {m : Nat} (hm : m < 128) : y0OK m = true := by
  have h : ∀ s < 4, y0Sl s = true := by
    intro s hs
    interval_cases s
    exacts [y0Sl0, y0Sl1, y0Sl2, y0Sl3]
  have := allBlk_spec (h (m / 32) (by omega)) (m % 32) (by omega)
  rwa [show Nat.add (Nat.mul 32 (m / 32)) (m % 32) = m by
    change 32 * (m / 32) + m % 32 = m
    omega] at this

theorem cAOK_of {m : Nat} (hm : m < 128) : cAOK m = true := by
  have h : ∀ s < 4, cASl s = true := by
    intro s hs
    interval_cases s
    exacts [cASl0, cASl1, cASl2, cASl3]
  have := allBlk_spec (h (m / 32) (by omega)) (m % 32) (by omega)
  rwa [show Nat.add (Nat.mul 32 (m / 32)) (m % 32) = m by
    change 32 * (m / 32) + m % 32 = m
    omega] at this

theorem nAOK_of {m : Nat} (hm : m < 256) : nAOK m = true := by
  have h : ∀ s < 8, nASl s = true := by
    intro s hs
    interval_cases s
    exacts [nASl0, nASl1, nASl2, nASl3, nASl4, nASl5, nASl6, nASl7]
  have := allBlk_spec (h (m / 32) (by omega)) (m % 32) (by omega)
  rwa [show Nat.add (Nat.mul 32 (m / 32)) (m % 32) = m by
    change 32 * (m / 32) + m % 32 = m
    omega] at this

theorem pR0K {q : Nat} (hq : q < 4) : P r0Tabs[q]! (r0K q) := by
  interval_cases q
  · exact pId'
  · exact pw0
  · exact pr1
  · exact pr2

theorem y0Tabs_get {X p : Nat} (hX : X < 2) (hp : p < 64) :
    (y0Tabs[X]!)[p]! = comp 1782 ttabs[radK X (p / 4)]! r0Tabs[p % 4]! := by
  have e : y0Tabs[X]! = y0TabsOf X := by interval_cases X <;> rfl
  rw [e]
  unfold y0TabsOf
  rw [ofFn_get' _ hp, rads_get hX]
  rfl

theorem pY {X p : Nat} (hX : X < 2) (hp : p < 64) : P (y0Tabs[X]!)[p]! (SuzGlY (64 * X + p)) := by
  rw [y0Tabs_get hX hp]
  have h := y0OK_of (m := 64 * X + p) (by omega)
  unfold y0OK at h
  rw [show Nat.div (64 * X + p) 64 = X by change (64 * X + p) / 64 = X; omega,
    show Nat.div (Nat.mod (64 * X + p) 64) 4 = p / 4 by change (64 * X + p) % 64 / 4 = p / 4; omega,
    show Nat.mod (64 * X + p) 4 = p % 4 by change (64 * X + p) % 4 = p % 4; omega] at h
  exact p_eq (pc' (pTT (radK_lt hX (by omega))) (pR0K (by omega))) h

theorem y0_size {X : Nat} (hX : X < 2) : (y0Tabs[X]!).size = 64 := by
  have e : y0Tabs[X]! = y0TabsOf X := by interval_cases X <;> rfl
  rw [e]
  simp [y0TabsOf]

theorem y0Fps_get {X z : Nat} (hX : X < 2) (hz : z < 1782) : (y0Fps[X]!)[z]! = fpY X z := by
  have e : y0Fps[X]! = fpIndex y0Tabs[X]! := by interval_cases X <;> rfl
  rw [e, fpIndex_get _ hz, y0_size hX]
  exact fpL_congr fun j hj => by
    rw [(pY hX hj).1, unpack_getElem! (by norm_num)]
    rfl

theorem cA_eq (X p : Nat) : (cActs[X]!)[p]! = cAK X p := by
  unfold cActs cAK
  by_cases hX : X < 2
  · rw [ofFn_get' _ hX, blt_t hX]
    by_cases hp : p < 64
    · rw [ofFn_get' _ hp, blt_t hp]
      have h := cAOK_of (m := 64 * X + p) (by omega)
      unfold cAOK at h
      rw [strictB_app', show Nat.div (64 * X + p) 64 = X by change (64 * X + p) / 64 = X; omega,
        strictB_app', strictB_app',
        show Nat.mod (64 * X + p) 64 = p by change (64 * X + p) % 64 = p; omega] at h
      obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
      obtain ⟨h, -⟩ := (bAnd_iff _ _).1 h
      have hc := pc' (pc' (pW hX) (pY hX hp)) (pWI hX)
      unfold y0Pos conjTab
      rw [hc.1, unpack_getElem! (by norm_num), y0Fps_get hX (pg_lt hc.2 (by norm_num))]
      exact Nat.eq_of_beq_eq_true h
    · rw [ofFn_neg' _ hp, blt_f hp]
      rfl
  · rw [ofFn_neg' _ hX, blt_f hX]
    rfl

theorem cA_conj {X p : Nat} (hX : X < 2) (hp : p < 64) : cAK X p < 64 ∧
    ((y0Tabs[X]!)[cAK X p]! == conjTab 1782 cTabsW[X]! cInvsW[X]! (y0Tabs[X]!)[p]!) = true := by
  have h := cAOK_of (m := 64 * X + p) (by omega)
  unfold cAOK at h
  rw [strictB_app', show Nat.div (64 * X + p) 64 = X by change (64 * X + p) / 64 = X; omega,
    strictB_app', strictB_app',
    show Nat.mod (64 * X + p) 64 = p by change (64 * X + p) % 64 = p; omega] at h
  obtain ⟨ha, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  have ha' : g7 (SuzGlK X) p < 64 := Eq.mp Nat.blt_eq ha
  have e : cAK X p = g7 (SuzGlK X) p := by
    unfold cAK
    rw [blt_t hX, blt_t hp]
  rw [e]
  refine ⟨ha', ?_⟩
  unfold conjTab
  rw [beqP (pY hX ha') (pc' (pc' (pW hX) (pY hX hp)) (pWI hX))]
  exact h

theorem nA_eq (l k : Nat) : (nActs[l]!)[k]! = nAK l k := by
  unfold nActs nAK
  by_cases hl : l < 4
  · rw [ofFn_get' _ hl, blt_t hl]
    by_cases hk : k < 64
    · rw [ofFn_get' _ hk, blt_t hk]
      have h := nAOK_of (m := 64 * l + k) (by omega)
      unfold nAOK at h
      rw [strictB_app', show Nat.div (64 * l + k) 64 = l by change (64 * l + k) / 64 = l; omega,
        show Nat.mod (64 * l + k) 64 = k by change (64 * l + k) % 64 = k; omega, strictB_app',
        strictB_app'] at h
      have hy := pc' (pc' (pN hl) (pTT hk)) (pNI hl)
      dsimp only
      unfold tFound conjTab
      rw [tPos_P hy]
      rw [Nat.eq_of_beq_eq_true h]
      generalize hj : fpT _ = j
      by_cases hj64 : j < 64
      · rw [beqP (pTT hj64) hy, blt_t hj64]
        cases Nat.beq (T j) _ <;> simp [hj64]
      · rw [blt_f hj64]
        simp [hj64]
    · rw [ofFn_neg' _ hk, blt_f hk]
      rfl
  · rw [ofFn_neg' _ hl, blt_f hl]
    rfl

end CertificateChecks.KernelSpor.SuzGl

end
