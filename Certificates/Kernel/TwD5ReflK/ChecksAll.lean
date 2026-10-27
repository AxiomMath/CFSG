module

public import Certificates.Data.Kernel.TwD5ReflK
public import Certificates.Kernel.TwD5ReflK.DataAll
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.TwD5RAll

open CFSG.KC.TwD5R

theorem ch709602gens : allL gensAll (validH false) = true := by quickRfl

theorem ch709602tab : tabOK reps repTab nrep = true := by quickRfl

theorem ch709602reps : repsOK goodsAll reps repsH repsB = true := by quickRfl

theorem ch709602repN : repNOK false (List.append goodsAll (fstL repsB)) = true := by quickRfl

theorem ch709602bad : badOK false gensAll repsB = true := by quickRfl

theorem ch709602k12 : k12OK false gensAll goodsAll k12 = true := by quickRfl

theorem ch709602lh : lhOK false gensAll repsH LH = true := by quickRfl

theorem ch709602lg0 : lgOK false gensAll 355268 LG0 = true := by quickRfl

theorem ch709602lg1 : lgOK false gensAll 236845 LG1 = true := by quickRfl

theorem ch709602lg2 : lgOK false gensAll 265354 LG2 = true := by quickRfl

theorem ch709602lg3 : lgOK false gensAll 442258 LG3 = true := by quickRfl

theorem ch709602k3a : k3OK gensAll 355268 LH LG0 OW0 = true := by quickRfl

theorem ch709602k3b : k3OK gensAll 236845 LH LG1 OW1 = true := by quickRfl

theorem ch709602k3c : k3OK gensAll 265354 LH LG2 OW2 = true := by quickRfl

theorem ch709602k3d : k3OK gensAll 442258 LH LG3 OW3 = true := by quickRfl

end CFSG.KD.TwD5RAll
