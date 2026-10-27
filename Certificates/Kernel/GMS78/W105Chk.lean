module

public import Certificates.Kernel.GMS78.W
public import Certificates.Data.GMS78RuAsmAlign
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.W

open CFSG.KC.Ord CFSG.KC.GMSW CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuAsm

@[expose] noncomputable def RAl : List (List (Nat × Bool)) :=
  [[(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, true), (4, true), (2, true), (4, true), (4, false), (2, false), (4, false), (2, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (4, false), (2, false), (4, false), (2, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false)],
   [(2, true), (4, true), (2, true), (4, true), (4, false), (2, false), (4, false), (2, false)],
   [(2, true), (4, true), (2, true), (4, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, true), (4, true), (2, true), (4, true), (2, true), (4, true), (2, true), (4, true)],
   [(2, true), (4, true), (2, true), (4, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false)],
   [(2, true), (4, true), (2, true), (4, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, true), (4, true), (2, true), (4, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false)],
   [(2, true), (4, true), (2, true), (4, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (4, false), (2, false), (4, false), (2, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (2, true), (4, true), (2, true), (4, true), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false)],
   [(5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false)],
   [(5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, true), (4, true), (2, true), (4, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false)],
   [(5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true)],
   [(5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, false), (2, false), (4, false), (2, false)],
   [(5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, true), (4, true), (2, true), (4, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, false), (2, false), (4, false), (2, false)],
   [(2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false)],
   [(2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, true), (4, true), (2, true), (4, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false)],
   [(2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, false), (2, false), (4, false), (2, false)],
   [(2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true)],
   [(2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, true), (4, true), (2, true), (4, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, false), (2, false), (4, false), (2, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true)],
   [(4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, true), (8, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (8, false), (2, false), (4, false), (2, false), (4, false), (2, false)],
   [(8, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (8, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, true), (6, true), (8, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (8, false), (6, false), (2, false), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false)],
   [(5, true), (6, true), (8, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (8, false), (6, false), (5, false), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(6, true), (8, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (8, false), (6, false), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false)],
   [(6, true), (2, true), (8, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (8, false), (2, false), (6, false), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, false), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (2, true), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, true), (2, true), (4, true), (2, true), (4, true), (2, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, false), (2, true), (4, true), (2, true), (4, true), (2, true), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, false), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(2, false), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (2, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false)],
   [(3, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (3, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(3, false), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (3, true), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(3, true), (2, true), (4, true), (2, true), (4, true), (3, false), (4, false), (2, false), (4, false), (2, false)],
   [(3, false), (2, true), (4, true), (2, true), (4, true), (3, true), (4, false), (2, false), (4, false), (2, false)],
   [(3, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (3, false), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false)],
   [(3, false), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (3, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false)],
   [(4, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (4, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, false), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (4, true), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (2, true), (4, true), (2, true), (4, true), (4, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, false), (2, true), (4, true), (2, true), (4, true), (4, true), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, false), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(4, false), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (4, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(5, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(5, false), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (5, true), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(5, true), (2, true), (4, true), (2, true), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false)],
   [(5, false), (2, true), (4, true), (2, true), (4, true), (5, true), (4, false), (2, false), (4, false), (2, false)],
   [(5, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (5, false), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(5, false), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (5, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(6, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (6, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(6, false), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (6, true), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(6, true), (2, true), (4, true), (2, true), (4, true), (6, false), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(6, false), (2, true), (4, true), (2, true), (4, true), (6, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(6, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (6, false), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false)],
   [(6, false), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (6, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false)],
   [(8, true), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (8, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(8, false), (4, true), (3, true), (4, false), (3, true), (2, true), (2, true), (8, true), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(8, true), (2, true), (4, true), (2, true), (4, true), (8, false), (4, false), (2, false), (4, false), (2, false)],
   [(8, false), (2, true), (4, true), (2, true), (4, true), (8, true), (4, false), (2, false), (4, false), (2, false)],
   [(8, true), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (8, false), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (4, false), (2, false), (4, false), (2, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)],
   [(8, false), (5, true), (4, false), (2, true), (5, true), (4, false), (2, true), (8, true), (2, false), (4, true), (5, false), (2, false), (4, true), (5, false), (2, false), (2, false), (3, false), (4, true), (3, false), (4, false)]]

theorem RAl_bd : relsBounded RAl (nat_lit 9) = true := by quickRfl

theorem RAl_len : Nat.beq (lenRels RAl) (nat_lit 106) = true := by quickRfl

theorem RAl_bind : relsEqK RAl (mkPairsK (ruAlignMulPairs ++ ruAlignTransPairs ++ ruAlignNormPairs)) = true := by quickRfl

theorem RAl_c0 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RAl (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 14) = true := by
  quickRfl

theorem RAl_c1 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RAl (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 14) (nat_lit 13) = true := by
  quickRfl

theorem RAl_c2 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RAl (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 27) (nat_lit 11) = true := by
  quickRfl

theorem RAl_c3 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RAl (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 38) (nat_lit 10) = true := by
  quickRfl

theorem RAl_c4 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RAl (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 48) (nat_lit 10) = true := by
  quickRfl

theorem RAl_c5 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RAl (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 58) (nat_lit 12) = true := by
  quickRfl

theorem RAl_c6 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RAl (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 70) (nat_lit 19) = true := by
  quickRfl

theorem RAl_c7 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RAl (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 89) (nat_lit 17) = true := by
  quickRfl

theorem RAl_all : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RAl (nat_lit 9) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 106) = true :=
  relsAll_join (c := nat_lit 106) (relsAll_join (c := nat_lit 89) (relsAll_join (c := nat_lit 70) (relsAll_join (c := nat_lit 58) (relsAll_join (c := nat_lit 48) (relsAll_join (c := nat_lit 38) (relsAll_join (c := nat_lit 27) (RAl_c0) RAl_c1 rfl rfl) RAl_c2 rfl rfl) RAl_c3 rfl rfl) RAl_c4 rfl rfl) RAl_c5 rfl rfl) RAl_c6 rfl rfl) RAl_c7 rfl rfl

end CertificateChecks.KernelGMS78.W

end
