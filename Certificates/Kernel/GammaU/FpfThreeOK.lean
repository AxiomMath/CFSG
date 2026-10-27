module

public import Certificates.Data.Kernel.GammaUFpfThreeK
public import Certificates.Kernel.GammaU.FpfThreeData

public section

namespace CFSG.KD.GUK

open CFSG.KC.GUK CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.SigmaP

theorem kf16972_b0 : six (kBasis 0) = B60 := by decide +kernel
theorem kf16972_b1 : six (kBasis 1) = B61 := by decide +kernel
theorem kf16972_cs0 : kCS (six (kBasis 0)) (s45 0) = CS0 := by decide +kernel
theorem kf16972_cs1 : kCS (six (kBasis 1)) (s45 1) = CS1 := by decide +kernel
theorem kf16972_sm0 : maskL s45_0 = SM0 := by decide +kernel
theorem kf16972_sm1 : maskL s45_1 = SM1 := by decide +kernel

theorem kf16972_h0 : headK [12, 48, 51] B60 s45_0 CS0 [12, 48, 51, 204, 768, 3072]
    (spanList [12, 48, 51, 204, 768, 3072]) = true := by decide +kernel
theorem kf16972_h1 : headK [5, 48, 136] B61 s45_1 CS1 [5, 48, 136, 320, 522, 3072]
    (spanList [5, 48, 136, 320, 522, 3072]) = true := by decide +kernel

theorem kf16972_t0a : triplesK B60 s45_0 [12, 48, 51, 63, 204] SM0 CS0 [12, 48, 51] = true := by
  decide +kernel
theorem kf16972_t0b : triplesK B60 s45_0 [207, 240, 252, 255, 768] SM0 CS0 [12, 48, 51] = true := by
  decide +kernel
theorem kf16972_t0c : triplesK B60 s45_0 [771, 780, 783, 819, 828] SM0 CS0 [12, 48, 51] = true := by
  decide +kernel
theorem kf16972_t0d : triplesK B60 s45_0 [831, 963, 972, 1008, 1011] SM0 CS0 [12, 48, 51] = true := by
  decide +kernel
theorem kf16972_t0e : triplesK B60 s45_0 [1020, 3072, 3084, 3120, 3123] SM0 CS0 [12, 48, 51] = true := by
  decide +kernel
theorem kf16972_t0f : triplesK B60 s45_0 [3135, 3264, 3267, 3276, 3279] SM0 CS0 [12, 48, 51] = true := by
  decide +kernel
theorem kf16972_t0g : triplesK B60 s45_0 [3315, 3324, 3327, 3843, 3855] SM0 CS0 [12, 48, 51] = true := by
  decide +kernel
theorem kf16972_t0h : triplesK B60 s45_0 [3888, 3891, 3903, 4032, 4035] SM0 CS0 [12, 48, 51] = true := by
  decide +kernel
theorem kf16972_t0i : triplesK B60 s45_0 [4044, 4047, 4083, 4092, 4095] SM0 CS0 [12, 48, 51] = true := by
  decide +kernel

theorem kf16972_t1a : triplesK B61 s45_1 [5, 48, 136, 184, 320] SM1 CS1 [5, 48, 136] = true := by
  decide +kernel
theorem kf16972_t1b : triplesK B61 s45_1 [325, 373, 461, 509, 522] SM1 CS1 [5, 48, 136] = true := by
  decide +kernel
theorem kf16972_t1c : triplesK B61 s45_1 [570, 575, 642, 647, 690] SM1 CS1 [5, 48, 136] = true := by
  decide +kernel
theorem kf16972_t1d : triplesK B61 s45_1 [695, 842, 890, 895, 1010] SM1 CS1 [5, 48, 136] = true := by
  decide +kernel
theorem kf16972_t1e : triplesK B61 s45_1 [1015, 3072, 3077, 3120, 3208] SM1 CS1 [5, 48, 136] = true := by
  decide +kernel
theorem kf16972_t1f : triplesK B61 s45_1 [3213, 3256, 3261, 3440, 3528] SM1 CS1 [5, 48, 136] = true := by
  decide +kernel
theorem kf16972_t1g : triplesK B61 s45_1 [3533, 3576, 3581, 3594, 3599] SM1 CS1 [5, 48, 136] = true := by
  decide +kernel
theorem kf16972_t1h : triplesK B61 s45_1 [3642, 3714, 3719, 3762, 3767] SM1 CS1 [5, 48, 136] = true := by
  decide +kernel
theorem kf16972_t1i : triplesK B61 s45_1 [3914, 3919, 3962, 4082, 4087] SM1 CS1 [5, 48, 136] = true := by
  decide +kernel

end CFSG.KD.GUK

end
