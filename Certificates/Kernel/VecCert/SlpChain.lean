module

public import Certificates.Kernel.VecCert.HomBound

public section

namespace CertificateChecks.KernelVec

open CFSG.KC.Ord

theorem slpSeg_chain {d w S T L H CM RM ONE LV HV nb Lg : Nat} {RB : Nat → Nat} (W St : Nat → Nat)
    (hc : constsOK 2 w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S) :
    ∀ n, (∀ k < n, Nat.beq (runSlp RB (mulR 2 w S d T L H CM RM) (validM 2 nb L H) ONE [W k]
      (St k)) (St (k + 1)) = true) →
    RegsIn d w S nb L H Lg RB (St 0) → RegsIn d w S nb L H Lg RB (St n)
  | 0, _, h0 => h0
  | n + 1, h, h0 => slpSeg_sound hc hnb (h n (Nat.lt_succ_self n))
      (slpSeg_chain W St hc hnb n (fun k hk => h k (Nat.lt_succ_of_lt hk)) h0)

end CertificateChecks.KernelVec

end
