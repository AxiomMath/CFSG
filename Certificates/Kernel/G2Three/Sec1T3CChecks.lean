module

public import Certificates.Data.Kernel.G2Three.Sec1T3C
public import Certificates.Kernel.G2Three.Sec1T3Data
public import Certificates.Kernel.G2Three.Sec1T3RG
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three.Sec1T3

open CFSG.KC.Loop

theorem s3c_rg : rgK LMP RG 408 = true := by quickRfl

theorem s3c_rgAll0 : rgAllK LMP OR RG 408 0 51 = true := by quickRfl
theorem s3c_rgAll1 : rgAllK LMP OR RG 408 51 51 = true := by quickRfl
theorem s3c_rgAll2 : rgAllK LMP OR RG 408 102 51 = true := by quickRfl
theorem s3c_rgAll3 : rgAllK LMP OR RG 408 153 51 = true := by quickRfl
theorem s3c_rgAll4 : rgAllK LMP OR RG 408 204 51 = true := by quickRfl
theorem s3c_rgAll5 : rgAllK LMP OR RG 408 255 51 = true := by quickRfl
theorem s3c_rgAll6 : rgAllK LMP OR RG 408 306 51 = true := by quickRfl
theorem s3c_rgAll7 : rgAllK LMP OR RG 408 357 51 = true := by quickRfl

theorem s3c_f14a : f14aK PT PC IV SQ 1 2 3 4 5 5 = true := by quickRfl

theorem s3c_f14b : f14bK PT PC IV SQ LMP RG 408 1 2 3 4 5 5 = true := by quickRfl

theorem s3c_f14c : f14cK PT PC IV SQ LMP RG 408 1 2 3 4 5 7 = true := by quickRfl

theorem s3c_f14d : f14dK PT PC IV SQ LMP 408 1 2 3 4 5 186 214 5 = true := by quickRfl

theorem s3c_f14e : f14eK PT PC IV SQ LMP 408 1 2 3 4 5 372 375 302 5 = true := by quickRfl

@[expose] def s3cW : List Nat := [199341, 262321, 264885, 131768, 186, 131261, 196821, 65750]

theorem s3c_f14f : f14fK PT PC IV SQ LMP 408 1 2 3 4 5 5 s3cW = true := by quickRfl

theorem s3c_f14g : f14gK PT PC IV SQ LMP 408 1 2 3 4 5 5 = true := by quickRfl

end CFSG.KD.G2Three.Sec1T3

end
