
module

public import Certificates.Kernel.Fi23M.ConjBase
import all Certificates.Kernel.Fi23M.ConjBase

public import Certificates.Kernel.Fi23M.Keys
import Certificates.Kernel.Fi23M.TreeK
import Certificates.Kernel.Fi23K.OrbEq
import CFSG.Certificates.Kernel.Spor.PChainSound
import CFSG.Certificates.Kernel.Spor.TabWords
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelFi23M

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.KD.Fi23K CFSG.KC.Fi23K CFSG.KC.Enum
  CFSG.Sporadic.Th.Native CFSG.KS.Raw.Orb

theorem key_size {k : Nat} (hk : k < 31671) : orbLit.keys[k]!.size = 253 := by
  have h := canonW_of_canonM (key_canon hk)
  unfold canonW at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem check_atW {k : Nat} (hk : k < 31671) :
    conjCheckAtW 253 matA matA matB matBi orbLit
      (fun X => (indexOfW orbLit.keys).getD X orbLit.keys.size) k = true := by
  have hs := orbLit_size
  have ha : ap orbLit.alpha k = tb G 39 k := ap_tabOf 39 hk
  have hb : ap orbLit.beta k = tb G 40 k := ap_tabOf 40 hk
  have ha' : ap orbLit.alpha k < orbLit.keys.size := by rw [ha, hs]; exact rng 39 (by norm_num) k hk
  have hb' : ap orbLit.beta k < orbLit.keys.size := by rw [hb, hs]; exact rng 40 (by norm_num) k hk
  have hpos : (indexOfW orbLit.keys).getD orbLit.keys[k]! orbLit.keys.size = k :=
    indexOfW_getD (fun i hi j hj => hinj' i (by omega) j (by omega)) (by omega)
  have c1 : canonW 253 orbLit.keys[k]! = true := canonW_of_canonM (key_canon hk)
  have e1 : eqW 253 (conjW 253 matA matA orbLit.keys[k]!) orbLit.keys[ap orbLit.alpha k]! = true := by
    rw [hA' k hk]
    exact eqW_self_of (key_size (by omega))
  have e2 : eqW 253 (conjW 253 matB matBi orbLit.keys[k]!) orbLit.keys[ap orbLit.beta k]! = true := by
    rw [hB' k hk]
    exact eqW_self_of (key_size (by omega))
  have ht := tree_conj hk
  unfold conjCheckAtW
  dsimp only
  rw [c1, hpos, e1, e2, ht, decide_eq_true ha', decide_eq_true hb']
  simp

theorem conj_okW (chunks : Nat) :
    conjOrbitOKW 253 matD matA matA matB matBi orbLit chunks = true := by
  have hs := orbLit_size
  unfold conjOrbitOKW
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨by rw [hs]; norm_num, by rw [hs]; norm_num⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [orbLit_root]
    exact eqW_self_of CFSG.Sporadic.Fi23.matD_facts.1
  · unfold CFSG.Sporadic.Th.Native.invoOK
    rw [CFSG.KS.TW.allIn_iff]
    intro i hi
    rw [hs] at hi
    have eA : orbLit.alpha = tabOf 39 := rfl
    rw [eA, ap_tabOf 39 hi, ap_tabOf 39 (rng 39 (by norm_num) i hi), (ord_pt hi).1, beq_self_eq_true]
  · unfold CFSG.Sporadic.Th.Native.order3OK
    rw [CFSG.KS.TW.allIn_iff]
    intro i hi
    rw [hs] at hi
    have h1 := rng 40 (by norm_num) i hi
    have eB : orbLit.beta = tabOf 40 := rfl
    rw [eB, ap_tabOf 40 hi, ap_tabOf 40 h1, ap_tabOf 40 (rng 40 (by norm_num) _ h1), (ord_pt hi).2,
      beq_self_eq_true]
  · exact CFSG.KS.PC.parAll_of fun k hk => check_atW (by rwa [hs] at hk)

end CertificateChecks.KernelFi23M

end
