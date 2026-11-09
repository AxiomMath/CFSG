module

public import Certificates.Kernel.KGC31M24.CosDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.KGC31M24.Data7217
public import Certificates.Kernel.KGC31M24.Checks7217
public import Certificates.Kernel.KGC31M24.Glue
public import CFSG.Certificates.Kernel.KGC31PNormGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.BfsPin
open CFSG.Quasithin.KGC31.M24 CertificateChecks.KernelSporSch

theorem kCosN : cosNK = true := by quickRfl

theorem kCos0T : (trPL 24 5 M24C2.LR M24C2.TR 4).all (fun L => L.all fun t =>
    pnormAll 24 5 r2P t (pinv 24 5 t)) = true := by quickRfl

theorem kCos0L : Nat.beq ((trPL 24 5 M24C2.LR M24C2.TR 4).map List.length).prod 21504 = true := by
  quickRfl

theorem kCos0 : cos0K = true := by
  have hok : pspanOK 24 5 r2P = true := by
    have hk := kCosN
    unfold cosNK at hk
    simp only [Bool.and_eq_true] at hk
    exact hk.1.2
  have hpp : ∀ L ∈ trPL 24 5 M24C2.LR M24C2.TR 4, ∀ t ∈ L, PP 24 5 t := by
    have h := kTR
    simp only [Bool.and_eq_true] at h
    exact fun L hL t ht => PP_of_permOK hsz (List.all_eq_true.1 (List.all_eq_true.1 h.1.1.1 L hL) t ht)
  have hT := kCos0T
  have hall : ∀ c ∈ cb0P, pnormAll 24 5 r2P c (pinv 24 5 c) = true :=
    pnormAll_pfilter hsz (ppL r2W) hok _
      (fun L hL t ht => ⟨hpp L hL t ht, List.all_eq_true.1 (List.all_eq_true.1 hT L hL) t ht⟩)
      _ [] (PP.id hsz) (pnormAll_pidn hsz (ppL r2W) hok) (fun _ h => absurd h List.not_mem_nil)
  have hlen : cb0P.length = 21504 := by
    unfold cb0P
    rw [pfilter_length, Nat.eq_of_beq_eq_true kCos0L]
  unfold cos0K
  rw [List.countP_eq_length.2 hall, hlen]
  rfl

end CertificateChecks.KernelKGC31M24

end
