module

public import Certificates.Data.Kernel.X2E6SylQ
public import Certificates.Kernel.X2E6Syl.Data
public import Certificates.Kernel.X2E6Syl.DataQ

public section

namespace CFSG.KD.X2E6Syl

open CFSG.KC.X2E6Syl

theorem ch880001q_gen : gw.map wordL = gen := by decide +kernel

theorem ch880001q_qel : qEls gw = qel := by decide +kernel

theorem ch880001q_fam : mel.map (famM qel) = fam := by decide +kernel

theorem ch880001q_tel : tEls qel = tel := by decide +kernel

theorem ch880001q_qOKQ : qOKQ gw gen qel = true := by decide +kernel

theorem ch880001q_famF : famF fam tel = true := by decide +kernel

theorem ch880001q_fixQ : fixQ qel mel fixS fixE fixY wit = true := by decide +kernel

theorem ch880001_q : qOK gw = true := by
  rw [qOK_eq, ch880001q_gen, ch880001q_qel]
  exact ch880001q_qOKQ

theorem ch880001_fam : famOK gw mel = true := by
  rw [famOK_eq, ch880001q_qel, ch880001q_fam, ch880001q_tel]
  exact ch880001q_famF

theorem ch880001_fix : fixOK gw mel fixS fixE fixY wit = true := by
  rw [fixOK_eq, ch880001q_qel]
  exact ch880001q_fixQ

end CFSG.KD.X2E6Syl

end
