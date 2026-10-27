
module

public import Certificates.Kernel.L34Pk.Data
public import Certificates.Data.Kernel.L34Pk
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelL34

open CFSG.KC.L34 CFSG.KC.WCnt CFSG.Quasithin.L34Amalgam

set_option maxRecDepth 100000

theorem k_a2 : a2CheckP gL giL = true := by quickRfl
theorem k_pq : pqCheckP gL giL cL = true := by quickRfl
theorem k_inv : invCheckP gL giL cL = true := by quickRfl
theorem k_conj : conjCheckP gL giL = true := by quickRfl
theorem k_s1 : s1CheckP gL giL = true := by quickRfl
theorem k_rh : rhCheckP gL giL = true := by quickRfl
theorem k_glue : glueCheckP gL giL cL = true := by quickRfl

theorem k_crd : ∀ x : Fin 16,
    pm (pm (pm (if bit 0 x then cL.getD 1 0 else pI) (if bit 1 x then cL.getD 2 0 else pI))
      (if bit 2 x then cL.getD 4 0 else pI)) (if bit 3 x then cL.getD 8 0 else pI) =
        cL.getD x.val 0 := by
  decide +kernel

theorem k_amal : amalRels.all (fun w => Nat.beq (pevT (fun j => gL.getD j.val 0)
    (fun j => giL.getD j.val 0) w) pI) = true := by quickRfl

theorem k_extra : (List.finRange 12).all (fun i => !decide (IsGood i) ||
    Nat.beq (pevT (fun j => gL.getD j.val 0) (fun j => giL.getD j.val 0)
      ((letter 's' :: word (repStr i)) ++ (letter 's' :: word (repStr i)) ++
        (letter 's' :: word (repStr i)))) pI) = true := by quickRfl

theorem k_c2 : (cWords.map fun s => pfold labC2 s.toList pI) = c2L := by decide +kernel

theorem k_c2L : c2L.Nodup := by decide +kernel

end CertificateChecks.KernelL34

end
