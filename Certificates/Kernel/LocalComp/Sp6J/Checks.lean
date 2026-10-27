module

public import Certificates.Kernel.LocalComp.Sp6J.ClsX
public import Certificates.Kernel.LocalComp.Sp6J.ClsC
public import Certificates.Kernel.LocalComp.Sp6J.CntC
public import Certificates.Kernel.Sporadic.Co3.Sp36
public import Certificates.Data.Kernel.Child3
public import Certificates.Data.Kernel.J2Cover
public import Certificates.Data.Kernel.SporSch.MathieuBT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Sp6J

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KC.Child3
open CFSG.KS.M11 CFSG.KS.SporSch.MBT CFSG.EvenSmallLie.Sp6 CertificateChecks.KernelSpor

theorem kSz : szOK 36 6 = true := by quickRfl

theorem kId : idK 36 6 (mask 6) = true := by quickRfl

theorem kOne : canonK 36 6 (mask 6) (36 * 6) One36 = true := by quickRfl

theorem kImgA : CFSG.Monster.B.Mathieu.imageList sp6A = (unpack 36 6 (XQ.S 0)).toList := by
  decide +kernel

theorem kImgB : CFSG.Monster.B.Mathieu.imageList sp6B = (unpack 36 6 (XQ.S 1)).toList := by
  decide +kernel

theorem kPX : allN 10 (fun j => permOK 36 6 (mask 6) (36 * 6) (XQ.S j) (XQ.SI j)) = true := by
  quickRfl

theorem kCX : allN 2 (fun j => bAnd(canonK 36 6 (mask 6) (36 * 6) (XQ.S j),
    canonK 36 6 (mask 6) (36 * 6) (XQ.SI j))) = true := by quickRfl

theorem kNX : Nat.beq (ordK XQ.LR 6) 1451520 = true := by quickRfl

theorem kWX : allN sp6InvRepWords.length (fun i => bAnd(lettersK 2 (sp6InvRepWords.getD i []),
    Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI (sp6InvRepWords.getD i []))
      (RX.E (lget RX.OFF i)))) = true := by quickRfl

theorem kOX : allN sp6InvRepWords.length (fun i => bAnd(canonK 36 6 (mask 6) (36 * 6)
    (RX.E (lget RX.OFF i)), ordIs 36 6 (mask 6) (pidn 36 6) (RX.E (lget RX.OFF i)) (2 - 1))) =
    true := by quickRfl

theorem kOffX : offOK RX.CS RX.OFF RX.N = true := by quickRfl

theorem kPosX : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) RX.CS = true := by quickRfl

theorem kRX : allN RX.N (repK 36 6 XQ.S XQ.SI 2 RX.CS RX.OFF RX.CI RX.E RX.P RX.L RX.K RX.S
    RX.SI RX.N 4000) = true := by quickRfl

theorem kCSX : RX.CS = [63, 315, 945, 3780] := by decide +kernel

theorem kSift : allN 2 (fun k => bAnd(Co3Text36.hiOK (XQ.S k), Co3Sp36.sift (XQ.S k))) = true := by
  quickRfl

theorem kG1 : allN c1Words.length (fun j => bAnd(lettersK 2 (c1Words.getD j []),
    Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI (c1Words.getD j [])) (C1Q.S j))) =
    true := by quickRfl

theorem kP1 : allN 5 (fun j => permOK 36 6 (mask 6) (36 * 6) (C1Q.S j) (C1Q.SI j)) = true := by
  quickRfl

theorem kC1 : allN 5 (fun j => bAnd(canonK 36 6 (mask 6) (36 * 6) (C1Q.S j),
    canonK 36 6 (mask 6) (36 * 6) (C1Q.SI j))) = true := by quickRfl

theorem kM1 : allN 5 (fun j => commK 36 6 (mask 6) (36 * 6) (C1Q.S j) (RX.E (lget RX.OFF 0))) =
    true := by quickRfl

theorem kN1 : Nat.beq (ordK C1Q.LR 5) 23040 = true := by quickRfl

theorem kT1 : Nat.beq N1.CS.sum RF1.N = true := by quickRfl

theorem kW1 : allN f1Words.length (fun i => bAnd(lettersK 5 (f1Words.getD i []),
    Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) C1Q.S C1Q.SI (f1Words.getD i []))
      (RF1.E (lget RF1.OFF i)))) = true := by quickRfl

theorem kO1 : allN f1Words.length (fun i => bAnd(canonK 36 6 (mask 6) (36 * 6)
    (RF1.E (lget RF1.OFF i)), ordIs 36 6 (mask 6) (pidn 36 6) (RF1.E (lget RF1.OFF i)) (4 - 1))) =
    true := by quickRfl

theorem kOff1 : offOK RF1.CS RF1.OFF RF1.N = true := by quickRfl

theorem kPos1 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) RF1.CS = true := by quickRfl

theorem kR1 : allN RF1.N (repK 36 6 C1Q.S C1Q.SI 5 RF1.CS RF1.OFF RF1.CI RF1.E RF1.P RF1.L RF1.K
    RF1.S RF1.SI RF1.N 4000) = true := by quickRfl

theorem kG2 : allN c2Words.length (fun j => bAnd(lettersK 2 (c2Words.getD j []),
    Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI (c2Words.getD j [])) (C2Q.S j))) =
    true := by quickRfl

theorem kP2 : allN 3 (fun j => permOK 36 6 (mask 6) (36 * 6) (C2Q.S j) (C2Q.SI j)) = true := by
  quickRfl

theorem kC2 : allN 3 (fun j => bAnd(canonK 36 6 (mask 6) (36 * 6) (C2Q.S j),
    canonK 36 6 (mask 6) (36 * 6) (C2Q.SI j))) = true := by quickRfl

theorem kM2 : allN 3 (fun j => commK 36 6 (mask 6) (36 * 6) (C2Q.S j) (RX.E (lget RX.OFF 1))) =
    true := by quickRfl

theorem kN2 : Nat.beq (ordK C2Q.LR 4) 4608 = true := by quickRfl

theorem kT2 : Nat.beq N2.CS.sum RF2.N = true := by quickRfl

theorem kW2 : allN f2Words.length (fun i => bAnd(lettersK 3 (f2Words.getD i []),
    Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) C2Q.S C2Q.SI (f2Words.getD i []))
      (RF2.E (lget RF2.OFF i)))) = true := by quickRfl

theorem kO2 : allN f2Words.length (fun i => bAnd(canonK 36 6 (mask 6) (36 * 6)
    (RF2.E (lget RF2.OFF i)), ordIs 36 6 (mask 6) (pidn 36 6) (RF2.E (lget RF2.OFF i)) (4 - 1))) =
    true := by quickRfl

theorem kOff2 : offOK RF2.CS RF2.OFF RF2.N = true := by quickRfl

theorem kPos2 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) RF2.CS = true := by quickRfl

theorem kR2 : allN RF2.N (repK 36 6 C2Q.S C2Q.SI 3 RF2.CS RF2.OFF RF2.CI RF2.E RF2.P RF2.L RF2.K
    RF2.S RF2.SI RF2.N 4000) = true := by quickRfl

theorem kG3 : allN c3Words.length (fun j => bAnd(lettersK 2 (c3Words.getD j []),
    Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI (c3Words.getD j [])) (C3Q.S j))) =
    true := by quickRfl

theorem kP3 : allN 6 (fun j => permOK 36 6 (mask 6) (36 * 6) (C3Q.S j) (C3Q.SI j)) = true := by
  quickRfl

theorem kC3 : allN 6 (fun j => bAnd(canonK 36 6 (mask 6) (36 * 6) (C3Q.S j),
    canonK 36 6 (mask 6) (36 * 6) (C3Q.SI j))) = true := by quickRfl

theorem kM3 : allN 6 (fun j => commK 36 6 (mask 6) (36 * 6) (C3Q.S j) (RX.E (lget RX.OFF 2))) =
    true := by quickRfl

theorem kN3 : Nat.beq (ordK C3Q.LR 4) 1536 = true := by quickRfl

theorem kT3 : Nat.beq N3.CS.sum RF3.N = true := by quickRfl

theorem kW3 : allN f3Words.length (fun i => bAnd(lettersK 6 (f3Words.getD i []),
    Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) C3Q.S C3Q.SI (f3Words.getD i []))
      (RF3.E (lget RF3.OFF i)))) = true := by quickRfl

theorem kO3 : allN f3Words.length (fun i => bAnd(canonK 36 6 (mask 6) (36 * 6)
    (RF3.E (lget RF3.OFF i)), ordIs 36 6 (mask 6) (pidn 36 6) (RF3.E (lget RF3.OFF i)) (4 - 1))) =
    true := by quickRfl

theorem kOff3 : offOK RF3.CS RF3.OFF RF3.N = true := by quickRfl

theorem kPos3 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) RF3.CS = true := by quickRfl

theorem kR3 : allN RF3.N (repK 36 6 C3Q.S C3Q.SI 6 RF3.CS RF3.OFF RF3.CI RF3.E RF3.P RF3.L RF3.K
    RF3.S RF3.SI RF3.N 4000) = true := by quickRfl

theorem kG4 : allN c4Words.length (fun j => bAnd(lettersK 2 (c4Words.getD j []),
    Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI (c4Words.getD j [])) (C4Q.S j))) =
    true := by quickRfl

theorem kP4 : allN 6 (fun j => permOK 36 6 (mask 6) (36 * 6) (C4Q.S j) (C4Q.SI j)) = true := by
  quickRfl

theorem kC4 : allN 6 (fun j => bAnd(canonK 36 6 (mask 6) (36 * 6) (C4Q.S j),
    canonK 36 6 (mask 6) (36 * 6) (C4Q.SI j))) = true := by quickRfl

theorem kM4 : allN 6 (fun j => commK 36 6 (mask 6) (36 * 6) (C4Q.S j) (RX.E (lget RX.OFF 3))) =
    true := by quickRfl

theorem kN4 : Nat.beq (ordK C4Q.LR 4) 384 = true := by quickRfl

theorem kT4 : Nat.beq N4.CS.sum RF4.N = true := by quickRfl

theorem kW4 : allN f4Words.length (fun i => bAnd(lettersK 6 (f4Words.getD i []),
    Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) C4Q.S C4Q.SI (f4Words.getD i []))
      (RF4.E (lget RF4.OFF i)))) = true := by quickRfl

theorem kO4 : allN f4Words.length (fun i => bAnd(canonK 36 6 (mask 6) (36 * 6)
    (RF4.E (lget RF4.OFF i)), ordIs 36 6 (mask 6) (pidn 36 6) (RF4.E (lget RF4.OFF i)) (4 - 1))) =
    true := by quickRfl

theorem kOff4 : offOK RF4.CS RF4.OFF RF4.N = true := by quickRfl

theorem kPos4 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) RF4.CS = true := by quickRfl

theorem kR4 : allN RF4.N (repK 36 6 C4Q.S C4Q.SI 6 RF4.CS RF4.OFF RF4.CI RF4.E RF4.P RF4.L RF4.K
    RF4.S RF4.SI RF4.N 4000) = true := by quickRfl

end CertificateChecks.KernelLC.Sp6J

end
