module

public import Certificates.Kernel.Sp62L.SmallChecks
public import CFSG.Certificates.Kernel.Sp62L.TabSound

public section

namespace CertificateChecks.KernelSp62L

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.Quasithin.G2U CFSG.KGroups.Sp6 CFSG.KC.Sp62L

theorem chkT_ok : chkT = true := by
  obtain ⟨ht, hc, hn⟩ := of_replayB ch9440rt_
  exact tabCheck_of ht hc hn ch9440t_

theorem chkB_ok : chkB = true := by
  obtain ⟨ht, hc, hn⟩ := of_replayB ch9440rb_
  refine tabCheck_of ht hc hn ?_
  rw [propB, propB1, (of_replayB ch9440rt_).1]
  exact ch9440b_

theorem chkE_ok : chkE = true := by
  obtain ⟨ht, hc, hn⟩ := of_replayB ch9440re_
  refine tabCheck_of ht hc hn ?_
  rw [propE, propE1, (of_replayB ch9440rt_).1]
  exact ch9440e_

theorem chkD_ok : chkD = true := by
  obtain ⟨ht, hc, hn⟩ := of_replayB ch9440rd_
  refine tabCheck_of ht hc hn ?_
  rw [propD, propD1, (of_replayB ch9440re_).1]
  exact ch9440d_

theorem check5169 : allCheck (fun x => !(commB x cSg) || inZ x) (tabOf gensB 27) = true := by
  rw [(of_replayB ch9440rb_).1]
  exact ch5169_

end CertificateChecks.KernelSp62L

end
