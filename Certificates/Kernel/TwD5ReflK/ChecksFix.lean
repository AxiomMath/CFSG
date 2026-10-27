module

public import Certificates.Data.Kernel.TwD5ReflK
public import Certificates.Kernel.TwD5ReflK.DataFix
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.TwD5RFix

open CFSG.KC.TwD5R

theorem ch709601gens : allL gensFix (validH true) = true := by quickRfl

theorem ch709601tab : tabOK reps repTab nrep = true := by quickRfl

theorem ch709601reps : repsOK goodsFix reps repsH repsB = true := by quickRfl

theorem ch709601repN : repNOK true (List.append goodsFix (fstL repsB)) = true := by quickRfl

theorem ch709601bad : badOK true gensFix repsB = true := by quickRfl

theorem ch709601k12 : k12OK true gensFix goodsFix k12 = true := by quickRfl

theorem ch709601lh : lhOK true gensFix repsH LH = true := by quickRfl

theorem ch709601lg0 : lgOK true gensFix 236845 LG0 = true := by quickRfl

theorem ch709601lg1 : lgOK true gensFix 265354 LG1 = true := by quickRfl

theorem ch709601lg2 : lgOK true gensFix 442258 LG2 = true := by quickRfl

theorem ch709601k3a : k3OK gensFix 236845 LH LG0 OW0 = true := by quickRfl

theorem ch709601k3b : k3OK gensFix 265354 LH LG1 OW1 = true := by quickRfl

theorem ch709601k3c : k3OK gensFix 442258 LH LG2 OW2 = true := by quickRfl

end CFSG.KD.TwD5RFix
