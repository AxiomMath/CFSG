module

public import Certificates.Kernel.Prim77.Checks
public import CFSG.Certificates.Kernel.Prim77Sound

public section

namespace CFSG.KD.Prim77

open CFSG.KC.Enum CFSG.KC.Over77 CFSG.KC.Prim77 CFSG.KS.Prim77 CFSG.KD.Over77
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77

theorem c12634 : primCheck = true := by
  have hb := c12634base
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨b0, b2⟩, b3⟩, b4⟩ := hb
  have hA := ar_of_arK b0
  have hC := ar_of_arK b2
  have hg := ar_let5 hA hC
  have ht := c12634trans
  simp only [letsB_eq] at ht
  obtain ⟨W, hW, hWk⟩ := optB_spec ht
  have hT : chkTrans = true := by
    refine chkTrans_of hg (W := W) ?_ hWk
    rw [transWords, Tc.eq]
    exact parseWords_of hW
  have hs := c12634stab
  simp only [letsB_eq] at hs
  obtain ⟨W2, hW2, hs2⟩ := optB_spec hs
  obtain ⟨R, hR, hRk⟩ := optB_spec hs2
  have hS : chkStab = true := by
    refine chkStab_of hg (W := W2) (R := R) ?_ ?_ hRk
    · rw [stabWords, Sc.eq]
      exact parseWords_of hW2
    · rw [repArr, Rc.eq]
      exact parseNats_of hR
  have ho := c12634ord
  simp only [letsB_eq] at ho
  have hO : chkOrders = true := chkOrders_of hA hC (ar_of_arK b3) (ar_of_arK b4) ho
  unfold primCheck
  rw [hT, hS, hO]
  rfl

end CFSG.KD.Prim77

end
