module

public import Certificates.Kernel.Misc.OrbData
public import Certificates.Kernel.Misc.XiD.TP
public import Certificates.Kernel.Misc.XiD.HS
public import Certificates.Kernel.Misc.XiD.ML
public import Certificates.Kernel.Misc.XiD.RW
public import Certificates.Kernel.Misc.XiD.AB
public import Certificates.Kernel.Misc.XiD.MT
public import Certificates.Kernel.Misc.LinesData
public import Certificates.Kernel.Misc.T46Data
public import Certificates.Kernel.Misc.Unitary
public import Certificates.Data.Kernel.Misc.Xi
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 200000

namespace CFSG.KD.Misc.Xi

open CFSG.KC.Misc.T46 CFSG.KC.Misc.Xi CFSG.KD.Misc.T46 CFSG.KD.Misc.Lines

theorem xP : Nat.beq XP (powP 3 (wordG GP [30, 33, 16, 12, 9, 39, 39])) = true := by quickRfl
theorem yP : Nat.beq YP (powP 2 (wordG GP [41, 46, 21, 23, 36])) = true := by quickRfl
theorem distinct : distinctK HS SP = true := by quickRfl
theorem orb0 : orbK UP XP YP HS ML J0 0 1 = true := by quickRfl
theorem orb1 : orbK UP XP YP HS ML J1 1 2 = true := by quickRfl
theorem orb2 : orbK UP XP YP HS ML J2 2 3 = true := by quickRfl
theorem inter : interK HS AB PB = true := by quickRfl
theorem memAll : ∀ k < 12, memK HS ML (352 * k) 352 = true := by kc_cover 1
theorem pa : paK J0 PA = true := by quickRfl
theorem row0 : rowsK TP HS ML RW AB 0 1 = true := by quickRfl
theorem rowsAll : ∀ k < 11, rowsR HS RW AB XP YP J0 PA (128 * k) 128 = true := by kc_cover 1
theorem conjAll : ∀ k < 21, conjK TP XP YP (33 * k) 33 = true := by kc_cover 1
theorem symAll : ∀ k < 11, symK AB (128 * k) 128 = true := by kc_cover 1
theorem diamAll : ∀ k < 11, diamK AB (128 * k) 128 = true := by kc_cover 1
theorem muAll : ∀ k < 11, muK AB MT (128 * k) 128 = true := by kc_cover 1

end CFSG.KD.Misc.Xi

end
