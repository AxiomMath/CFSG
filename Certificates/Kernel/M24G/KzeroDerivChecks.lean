module

public import Certificates.Data.Kernel.M24G.KzeroDeriv
public import Certificates.Kernel.M24G.KzeroData
public import Certificates.Kernel.M24G.KzeroDerivData
public import Certificates.Kernel.M24G.SliceIdx
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.KzeroC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

theorem kzDerivAll_ok_p0 : (SliceGlue.slice (KzeroD.kL.zip KzeroDD.kD) (0 * 8) 8).all
    (fun kd => duadEqT kd.1 Native.kzeroId || kzDerivF (Native.kzeroHs ()) KzeroD.kL kd.1 kd.2) = true := by
  quickRfl

theorem kzDerivAll_ok_p1 : (SliceGlue.slice (KzeroD.kL.zip KzeroDD.kD) (1 * 8) 8).all
    (fun kd => duadEqT kd.1 Native.kzeroId || kzDerivF (Native.kzeroHs ()) KzeroD.kL kd.1 kd.2) = true := by
  quickRfl

theorem kzDerivAll_ok_p2 : (SliceGlue.slice (KzeroD.kL.zip KzeroDD.kD) (2 * 8) 8).all
    (fun kd => duadEqT kd.1 Native.kzeroId || kzDerivF (Native.kzeroHs ()) KzeroD.kL kd.1 kd.2) = true := by
  quickRfl

theorem kzDerivAll_ok_p3 : (SliceGlue.slice (KzeroD.kL.zip KzeroDD.kD) (3 * 8) 8).all
    (fun kd => duadEqT kd.1 Native.kzeroId || kzDerivF (Native.kzeroHs ()) KzeroD.kL kd.1 kd.2) = true := by
  quickRfl

theorem kzDerivAll_ok_p4 : (SliceGlue.slice (KzeroD.kL.zip KzeroDD.kD) (4 * 8) 8).all
    (fun kd => duadEqT kd.1 Native.kzeroId || kzDerivF (Native.kzeroHs ()) KzeroD.kL kd.1 kd.2) = true := by
  quickRfl

theorem kzDerivAll_ok_p5 : (SliceGlue.slice (KzeroD.kL.zip KzeroDD.kD) (5 * 8) 8).all
    (fun kd => duadEqT kd.1 Native.kzeroId || kzDerivF (Native.kzeroHs ()) KzeroD.kL kd.1 kd.2) = true := by
  quickRfl

theorem kzDerivAll_ok_p6 : (SliceGlue.slice (KzeroD.kL.zip KzeroDD.kD) (6 * 8) 8).all
    (fun kd => duadEqT kd.1 Native.kzeroId || kzDerivF (Native.kzeroHs ()) KzeroD.kL kd.1 kd.2) = true := by
  quickRfl

theorem kzDerivAll_ok_p7 : (SliceGlue.slice (KzeroD.kL.zip KzeroDD.kD) (7 * 8) 8).all
    (fun kd => duadEqT kd.1 Native.kzeroId || kzDerivF (Native.kzeroHs ()) KzeroD.kL kd.1 kd.2) = true := by
  quickRfl

theorem kzDerivAll_ok : kzDerivAllF (Native.kzeroHs ()) KzeroD.kL KzeroDD.kD = true := by
  unfold kzDerivAllF
  rw [Bool.and_eq_true]
  exact ⟨by quickRfl, SliceGlue.all_of_slices _ 8 8 _ (Nat.le_of_ble_eq_true (by quickRfl)) fun j hj => match j, hj with
    | 0, _ => kzDerivAll_ok_p0
    | 1, _ => kzDerivAll_ok_p1
    | 2, _ => kzDerivAll_ok_p2
    | 3, _ => kzDerivAll_ok_p3
    | 4, _ => kzDerivAll_ok_p4
    | 5, _ => kzDerivAll_ok_p5
    | 6, _ => kzDerivAll_ok_p6
    | 7, _ => kzDerivAll_ok_p7
    | _ + 8, h => absurd h (by omega)⟩

theorem kzeroUFix_ok : kzeroUFixF = true := by
  decide +kernel

end CFSG.KC.M24G.KzeroC
