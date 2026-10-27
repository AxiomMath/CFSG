
module

public import Certificates.Kernel.Fi23R.Group
public import CFSG.Monster.GMS.Fi23FusionCertInputs
import Certificates.Kernel.Fi23R.Hunt
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23R

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KD.Fi23K CFSG.KD.Fi23R CFSG.KS.Raw.Orb
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native CertificateChecks.KernelFi23M

theorem cntS_split (q : ℕ → Bool) (lo a b c d : ℕ) (hc : a + b = c) (hd : lo + a = d) :
    cntS q lo c = cntS q lo a + cntS q d b := by
  rw [← hc, ← hd, cntS_add]

theorem hunt_count : (List.range 31671).countP (fxW G w53) = 183 := by
  have h0 := hunt0_ok
  have h1 := hunt1_ok
  have h2 := hunt2_ok
  unfold hunt0 hCnt at h0
  unfold hunt1 hCnt at h1
  unfold hunt2 hCnt at h2
  replace h0 := Nat.eq_of_beq_eq_true h0
  replace h1 := Nat.eq_of_beq_eq_true h1
  replace h2 := Nat.eq_of_beq_eq_true h2
  rw [← cntS_zero, cntS_split _ 0 25000 6671 31671 25000 (by norm_num) (by norm_num),
    cntS_split _ 0 12500 12500 25000 12500 (by norm_num) (by norm_num), h0, h1, h2]

theorem wa_one (c x : ℕ) : wa G [c] x = lf G c x := by rw [wa_cons, wa_nil]

theorem hunt_ok : huntChecks orbLit 53 = true := by
  have hD := rw_dTab
  have h1 := rw_treeActTab (k := 1) (by norm_num)
  have h39 := rw_treeActTab (k := 39) (by norm_num)
  have h53 := rw_treeActTab (k := 53) (by norm_num)
  have hT := (rw_compT (rw_compT (rw_compT hD h1) h39) h53).word (v := w53) rfl
  have hp := hPts_ok
  unfold hPts at hp
  simp only [Bool.and_eq_true, Nat.beq_eq] at hp
  obtain ⟨⟨p43, p1⟩, p39⟩ := hp
  have a43 : CFSG.Sporadic.Th.Native.ap (dTab orbLit) 53 = 53 := by
    rw [hD.ap (by norm_num), wa_one, lf_eq, if_pos (by norm_num)]
    exact p43
  have a1 : CFSG.Sporadic.Th.Native.ap
      (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 1) 53 = 53 := by
    rw [h1.ap (by norm_num), wa_one, lf_eq, if_neg (by norm_num)]
    exact p1
  have a39 : CFSG.Sporadic.Th.Native.ap
      (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 39) 53 = 53 := by
    rw [h39.ap (by norm_num), wa_one, lf_eq, if_neg (by norm_num)]
    exact p39
  have hf : fixCount (compT 31671 (compT 31671 (compT 31671 (dTab orbLit)
      (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 1))
      (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 39))
      (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 53)) = 183 := by
    unfold fixCount
    rw [hT.countP, hunt_count]
  unfold huntChecks
  dsimp only
  rw [a43, a1, a39, hf] <;> decide

end CertificateChecks.KernelFi23R

end
