module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Quasithin.Vol2.KGFactC31HSData
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import CFSG.Quasithin.Vol2.KGFactC31HSData
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Quasithin.Vol2.KGFactC31CosetCheck
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31HS

open CFSG.KS.SporSch.MOCG CFSG.Quasithin.KGC31.HS

public meta def tA : Array Nat := CFSG.RankThree.Native.hs100Arr 0

public meta def tB : Array Nat := CFSG.RankThree.Native.hs100Arr 1

meta def GM : Array (Array Nat) := #[tA, tB]

public meta def gw (wd : List Int) : Array Nat :=
  wd.foldr (fun l acc => comp (if l = 1 then tA else tB) acc) (idA 100)

meta def repsL : List (Array Nat) := [tA, gw wB]

meta def SCA : Array (Array Nat) := strongOf 100 (caGenW.map gw).toArray caChainW
meta def SCR : Array (Array Nat) := strongOf 100 (crGenW.map gw).toArray crChainW
meta def ST0 : Array (Array Nat) := strongOf 100 (t0GenW.map gw).toArray t0ChainW
meta def SM16 : Array (Array Nat) := strongOf 100 (m16GenW.map gw).toArray m16ChainW
meta def SN8 : Array (Array Nat) := strongOf 100 (n8GenW.map gw).toArray n8ChainW
meta def SQ : Array (Array Nat) := strongOf 100 (qGenW.map gw).toArray qChainW

meta def bCA : Array Nat := #[0, 2, 3]
meta def b0123 : Array Nat := #[0, 1, 2, 3]
meta def bT0 : Array Nat := #[2, 0]
meta def b012 : Array Nat := #[0, 1, 2]
meta def b0 : Array Nat := #[0]

end CertificateChecks.KernelKGC31HS

#lc_reps CertificateChecks.KernelKGC31HS.RH 7 CertificateChecks.KernelKGC31HS.GM
  CertificateChecks.KernelKGC31HS.repsL

#ks_rawchain CertificateChecks.KernelKGC31HS.CCA 100 7 100 CertificateChecks.KernelKGC31HS.SCA
  CertificateChecks.KernelKGC31HS.bCA 2 CFSG.Quasithin.KGC31.HS.caChainW

#ks_rawchain CertificateChecks.KernelKGC31HS.CCR 100 7 100 CertificateChecks.KernelKGC31HS.SCR
  CertificateChecks.KernelKGC31HS.b0123 3 CFSG.Quasithin.KGC31.HS.crChainW

#ks_rawchain CertificateChecks.KernelKGC31HS.CT0 100 7 100 CertificateChecks.KernelKGC31HS.ST0
  CertificateChecks.KernelKGC31HS.bT0 3 CFSG.Quasithin.KGC31.HS.t0ChainW

#ks_rawchain CertificateChecks.KernelKGC31HS.CM16 100 7 100 CertificateChecks.KernelKGC31HS.SM16
  CertificateChecks.KernelKGC31HS.b0123 2 CFSG.Quasithin.KGC31.HS.m16ChainW

#ks_rawchain CertificateChecks.KernelKGC31HS.CN8 100 7 100 CertificateChecks.KernelKGC31HS.SN8
  CertificateChecks.KernelKGC31HS.b012 2 CFSG.Quasithin.KGC31.HS.n8ChainW

#ks_rawchain CertificateChecks.KernelKGC31HS.CQ 100 7 100 CertificateChecks.KernelKGC31HS.SQ
  CertificateChecks.KernelKGC31HS.b0 3 CFSG.Quasithin.KGC31.HS.qChainW

end
