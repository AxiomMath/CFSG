module

public import Certificates.Kernel.FiveStd.NoInvGlue

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five

local instance instFact5' : Fact (Nat.Prime 5) := fact5

local notation "ιF" => Mat.ιF (ZMod 5)

theorem conj_cands {k : Nat} (hk : k < 5) {d g c y w : E} (hd : validE d = true)
    (hgd : g = conjE d (decE (RP.getD k 0))) (hw : validE w = true) (hwy : conjE w g = y)
    (hc : validE c = true) (hcy : conjE c g = y) :
    ∃ j < CM.getD k 0, c = mulE w (conjE d (decE (f20 (CB.getD k 0) j))) := by
  obtain ⟨hrk, -, -, hcen, -⟩ := cls_glue k hk
  set R := decE (RP.getD k 0)
  have hg : validE g = true := by rw [hgd]; exact hM5.valid_conjE hd hrk
  have hdi := hM5.valid_inv _ hd
  have hwi := hM5.valid_inv _ hw
  have hwc := hM5.valid_mul _ _ hwi hc
  set z := conjE (invE d) (mulE (invE w) c) with hzd
  have hzv : validE z = true := hM5.valid_conjE hdi hwc
  have hz : ιF z = (ιF d)⁻¹ * ((ιF w)⁻¹ * ιF c) * ιF d := by
    rw [hzd, hM5.map_conjE hdi hwc, hM5.map_mul _ _ hwi hc, hM5.map_inv _ hd, hM5.map_inv _ hw, inv_inv]
  have hR : ιF R = (ιF d)⁻¹ * ιF g * ιF d := by
    rw [hgd, hM5.map_conjE hd hrk]
    group
  have e1 : ιF c * ιF g * (ιF c)⁻¹ = ιF w * ιF g * (ιF w)⁻¹ := by
    rw [← hM5.map_conjE hc hg, ← hM5.map_conjE hw hg, hcy, hwy]
  have e2 : ιF c * ιF g = ιF w * ιF g * (ιF w)⁻¹ * ιF c := by
    rw [← e1]
    group
  have hcomm : mulE z R = mulE R z := by
    apply hM5.inj _ _ (hM5.valid_mul _ _ hzv hrk) (hM5.valid_mul _ _ hrk hzv)
    rw [hM5.map_mul _ _ hzv hrk, hM5.map_mul _ _ hrk hzv]
    calc ιF z * ιF R = (ιF d)⁻¹ * (ιF w)⁻¹ * (ιF c * ιF g) * ιF d := by
          rw [hz, hR]
          group
      _ = (ιF d)⁻¹ * (ιF w)⁻¹ * (ιF w * ιF g * (ιF w)⁻¹ * ιF c) * ιF d := by rw [e2]
      _ = ιF R * ιF z := by
          rw [hz, hR]
          group
  obtain ⟨j, hj, hje⟩ := mem_decL.1 ((hcen z hzv).1 hcomm)
  refine ⟨j, hj, ?_⟩
  rw [hje]
  apply hM5.inj _ _ hc (hM5.valid_mul _ _ hw (hM5.valid_conjE hd hzv))
  rw [hM5.map_mul _ _ hw (hM5.valid_conjE hd hzv), hM5.map_conjE hd hzv, hz]
  group

end CertificateChecks.FiveStd

end
