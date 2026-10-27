module

public import Certificates.Kernel.Sporadic.Fi22.R2079N3x
public import Certificates.Kernel.Sporadic.Fi22.R2079N3
public import Certificates.Kernel.Sporadic.Fi22.R2079N4x
public import Certificates.Kernel.Sporadic.Fi22.R2079N4
public import Certificates.Kernel.Sporadic.Fi22.R2079P3
public import Certificates.Kernel.Sporadic.Fi22.R2079P42
public import Certificates.Kernel.Sporadic.Fi22.GS2079P3
public import Certificates.Kernel.Sporadic.Fi22.D2079
public import Certificates.Kernel.Sporadic.Fi22.T2079N3
public import Certificates.Kernel.Sporadic.Fi22.T2079H2
public import Certificates.Kernel.Sporadic.Fi22.H2066c2
public import Certificates.Kernel.Sporadic.Fi22.H2066c3
public import Certificates.Kernel.Sporadic.Fi22.H2066c4
public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import CFSG.Certificates.Kernel.Spor.SiftBKSound
public import CFSG.Certificates.Kernel.Spor.ConjTreeSound
public import CFSG.Certificates.Kernel.PermToolSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fo22M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.ConjTree CFSG.KC.PermTool

theorem sN3 : allN 7 (fun j => Nat.beq (Fo22N3x.S j) (Fo22N3.S j)) = true := by quickRfl
theorem sN4 : allN 7 (fun j => Nat.beq (Fo22N4x.S j) (Fo22N4.S j)) = true := by quickRfl
theorem sP3 : allN 11 (fun j => Nat.beq (Fo22GP3.PS j) (Fo22P3.S j)) = true := by quickRfl
theorem oN3 : bAnd(Nat.beq Fo22T.A3.F (Fo22N3.S 0), Nat.beq Fo22T.B3.F (Fo22N3.S 1)) = true := by
  quickRfl
theorem oN4 : bAnd(Nat.beq Fo22T.A4.F (Fo22N4.S 0), Nat.beq Fo22T.B4.F (Fo22N4.S 1)) = true := by
  quickRfl
theorem oP3 : bAnd(Nat.beq Fo22T.Pa3.F (Fo22P3.S 0), Nat.beq Fo22T.Pb3.F (Fo22P3.S 1)) = true := by
  quickRfl
theorem oP4 : bAnd(Nat.beq Fo22T.Pa4.F (Fo22P4.S 0), Nat.beq Fo22T.Pb4.F (Fo22P4.S 1)) = true := by
  quickRfl
theorem bN3x : allN 7 (fun t => Nat.beq (#[9, 0, 1, 2, 3, 6, 4] : Array Nat)[t]!
    (pg 12 (mask 12) Fo22N3x.BP t)) = true := by quickRfl
theorem bN3 : allN 4 (fun t => Nat.beq (#[9, 0, 1, 2] : Array Nat)[t]!
    (pg 12 (mask 12) Fo22N3.BP t)) = true := by quickRfl
theorem bN4x : allN 6 (fun t => Nat.beq (#[0, 1, 2, 3, 6, 4] : Array Nat)[t]!
    (pg 12 (mask 12) Fo22N4x.BP t)) = true := by quickRfl
theorem bN4 : allN 3 (fun t => Nat.beq (#[0, 1, 2] : Array Nat)[t]!
    (pg 12 (mask 12) Fo22N4.BP t)) = true := by quickRfl
theorem bP3 : allN 5 (fun t => Nat.beq (#[0, 1, 2, 4, 3] : Array Nat)[t]!
    (pg 11 (mask 11) Fo22P3.BP t)) = true := by quickRfl
theorem bGP3 : allN 5 (fun t => Nat.beq (#[0, 1, 2, 4, 3] : Array Nat)[t]!
    (pg 11 (mask 11) Fo22GP3.BP t)) = true := by quickRfl
theorem bP4 : allN 6 (fun t => Nat.beq (#[0, 1, 2, 4, 3, 5] : Array Nat)[t]!
    (pg 7 (mask 7) Fo22P4.BP t)) = true := by quickRfl
theorem bP2 : allN 6 (fun t => Nat.beq (#[0, 1, 2, 3, 5, 7] : Array Nat)[t]!
    (pg 5 (mask 5) Fo22P2.BP t)) = true := by quickRfl
theorem s0T3 : Nat.beq (Fo22T3.T 0) Fo22T.S03.F = true := by quickRfl
theorem s0T2 : Nat.beq (Fo22T2.T 0) Fo22T.S02.F = true := by quickRfl
theorem last3 : allN 3 (fun i => Nat.beq (rcnt (Fo22N3x.LR (Nat.add 4 i))) 1) = true := by quickRfl
theorem last4 : allN 3 (fun i => Nat.beq (rcnt (Fo22N4x.LR (Nat.add 3 i))) 1) = true := by quickRfl

theorem cnN3 : allN 7 (fun j => bAnd(Fi22X.cn (Fo22N3.S j),
    bAnd(Fi22X.cn (Fo22N3.SI j), permOK 3510 12 (mask 12) (3510 * 12) (Fo22N3.S j)
      (Fo22N3.SI j)))) = true := by quickRfl
theorem cnN4 : allN 7 (fun j => bAnd(Fi22X.cn (Fo22N4.S j),
    bAnd(Fi22X.cn (Fo22N4.SI j), permOK 3510 12 (mask 12) (3510 * 12) (Fo22N4.S j)
      (Fo22N4.SI j)))) = true := by quickRfl
theorem cnH3 : allN 9 (fun j => bAnd(Fi22X.cn (Fi22H3.SI j), permOK 3510 12 (mask 12) (3510 * 12)
    (Fi22H3.S j) (Fi22H3.SI j))) = true := by quickRfl
theorem cnH4 : allN 9 (fun j => bAnd(Fi22X.cn (Fi22H4.SI j), permOK 3510 12 (mask 12) (3510 * 12)
    (Fi22H4.S j) (Fi22H4.SI j))) = true := by quickRfl
theorem cnH2 : allN 3 (fun j => bAnd(Fi22X.cn (Fi22H2.S j), bAnd(Fi22X.cn (Fi22H2.SI j),
    permOK 3510 12 (mask 12) (3510 * 12) (Fi22H2.S j) (Fi22H2.SI j)))) = true := by quickRfl
theorem cnS02 : Fi22X.cn Fo22T.S02.F = true := by quickRfl
theorem cnS03 : Fi22X.cn Fo22T.S03.F = true := by quickRfl

theorem pN3 : allN 7 (fun j => Fi22X.siftP (Fo22N3.S j)) = true := by quickRfl
theorem pN4 : allN 7 (fun j => Fi22X.siftP (Fo22N4.S j)) = true := by quickRfl
theorem pS02 : Fi22X.siftP Fo22T.S02.F = true := by quickRfl

theorem hN3 : allN 2 (fun i => siftBK 3510 12 (mask 12) (3510 * 12) 6 Fi22H3.S Fi22H3.SI Fi22H3.LR
    Fi22H3.ST 19 6 0 (baseImK 12 (mask 12) 6 (Fo22N3.S i) Fi22H3.BP)) = true := by quickRfl
theorem hN4 : allN 2 (fun i => siftBK 3510 12 (mask 12) (3510 * 12) 6 Fi22H4.S Fi22H4.SI Fi22H4.LR
    Fi22H4.ST 16 6 0 (baseImK 12 (mask 12) 6 (Fo22N4.S i) Fi22H4.BP)) = true := by quickRfl
theorem hS02 : siftBK 3510 12 (mask 12) (3510 * 12) 6 Fi22H2.S Fi22H2.SI Fi22H2.LR Fi22H2.ST 9 6 0
    (baseImK 12 (mask 12) 6 Fo22T.S02.F Fi22H2.BP) = true := by quickRfl
theorem cN3 : allN 9 (fun j => allN 2 (fun i => siftBK 3510 12 (mask 12) (3510 * 12) 7 Fo22N3x.S
    Fo22N3x.SI Fo22N3x.LR Fo22N3x.ST 7 7 0
    (baseImK 12 (mask 12) 7 (pconj 3510 12 (Fi22H3.S j) (Fo22N3.S i) (Fi22H3.SI j)) Fo22N3x.BP)))
    = true := by quickRfl
theorem cN4 : allN 9 (fun j => allN 2 (fun i => siftBK 3510 12 (mask 12) (3510 * 12) 6 Fo22N4x.S
    Fo22N4x.SI Fo22N4x.LR Fo22N4x.ST 7 6 0
    (baseImK 12 (mask 12) 6 (pconj 3510 12 (Fi22H4.S j) (Fo22N4.S i) (Fi22H4.SI j)) Fo22N4x.BP)))
    = true := by quickRfl

theorem id3 : bAnd(idK 1575 11 (mask 11), canonK 1575 11 (mask 11) (1575 * 11) (pidn 1575 11)) =
    true := by quickRfl
theorem id4 : bAnd(idK 63 7 (mask 7), canonK 63 7 (mask 7) (63 * 7) (pidn 63 7)) = true := by
  quickRfl
theorem cP3 : bAnd(canonK 1575 11 (mask 11) (1575 * 11) (Fo22P3.S 0),
    canonK 1575 11 (mask 11) (1575 * 11) (Fo22P3.S 1)) = true := by quickRfl
theorem cP4 : bAnd(canonK 63 7 (mask 7) (63 * 7) (Fo22P4.S 0),
    canonK 63 7 (mask 7) (63 * 7) (Fo22P4.S 1)) = true := by quickRfl
theorem ord3 : bAnd(Nat.beq (powK 1575 11 (Fo22P3.S 0) 3) (pidn 1575 11),
    bAnd(Bool.not (Nat.beq (Fo22P3.S 0) (pidn 1575 11)),
    bAnd(Nat.beq (powK 1575 11 (Fo22P3.S 1) 5) (pidn 1575 11),
    bAnd(Bool.not (Nat.beq (powK 1575 11 (Fo22P3.S 1) 1) (pidn 1575 11)),
    bAnd(Nat.beq (powK 1575 11 (pcomp 1575 11 (mask 11) (Fo22P3.S 0) (Fo22P3.S 1)) 7)
      (pidn 1575 11),
    Bool.not (Nat.beq (pcomp 1575 11 (mask 11) (Fo22P3.S 0) (Fo22P3.S 1)) (pidn 1575 11))))))) =
    true := by quickRfl
theorem ord4 : bAnd(Nat.beq (powK 63 7 (Fo22P4.S 0) 3) (pidn 63 7),
    bAnd(Bool.not (Nat.beq (Fo22P4.S 0) (pidn 63 7)),
    bAnd(Nat.beq (powK 63 7 (Fo22P4.S 1) 8) (pidn 63 7),
    bAnd(Bool.not (Nat.beq (powK 63 7 (Fo22P4.S 1) 4) (pidn 63 7)),
    bAnd(Nat.beq (powK 63 7 (pcomp 63 7 (mask 7) (Fo22P4.S 0) (Fo22P4.S 1)) 7) (pidn 63 7),
    Bool.not (Nat.beq (pcomp 63 7 (mask 7) (Fo22P4.S 0) (Fo22P4.S 1)) (pidn 63 7))))))) =
    true := by quickRfl

end CertificateChecks.KernelSpor.Fo22M

end
