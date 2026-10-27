module

public import Certificates.Kernel.ReflExt.Checks708604
public import Certificates.Kernel.ReflExt.Checks708605
public import Certificates.Kernel.ReflExt.ChecksCan
public import CFSG.Certificates.Kernel.ReflExt.ReflExtKSound

public section

namespace CFSG.KD.RX708604

open CFSG.ReflExt CFSG.ReflExt.RXK CFSG.TwoNodeSmall.WitK

theorem e6_frame0 : ∃ T, verifyAll (e6Frame 6 0) T = true :=
  frameK_verify _ (nthK fd0 e6 0) (frameK_of_parts ch708604.f_0 ch708604.f_1 ch708604.f_2
    ch708604.f_3 ch708604.f_4) chCan708604.f_0

theorem e6_frame1 : ∃ T, verifyAll (e6Frame 7 1) T = true :=
  frameK_verify _ (nthK fd0 e6 1) (frameK_of_parts ch708604.f_5 ch708604.f_6 ch708604.f_7
    ch708604.f_8 ch708604.f_9) chCan708604.f_1

theorem e6_frame2 : ∃ T, verifyAll (e6Frame 7 0) T = true :=
  frameK_verify _ (nthK fd0 e6 2) (frameK_of_parts ch708604.f_10 ch708604.f_11 ch708604.f_12
    ch708604.f_13 ch708604.f_14) chCan708604.f_2

theorem a5_frame0 : ∃ T, verifyAll (a5Frame 5) T = true :=
  frameK_verify _ (nthK fd0 a5 0) (frameK_of_parts ch708605.f_0 ch708605.f_1 ch708605.f_2
    ch708605.f_3 ch708605.f_4) chCan708604.f_3

theorem a5_frame1 : ∃ T, verifyAll (a5Frame 6) T = true :=
  frameK_verify _ (nthK fd0 a5 1) (frameK_of_parts ch708605.f_5 ch708605.f_6 ch708605.f_7
    ch708605.f_8 ch708605.f_9) chCan708604.f_4

end CFSG.KD.RX708604

end
