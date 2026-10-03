/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaS — root of the ζ follow-up library (RH-72 follow-up; plan `mathsrh/rh72/LEAN_PLAN.md`,
board `mathsrh/rh72/lean_board/BOARD.md`). Imports the trunk `Zeta23`.

Layout (first integration, 28 Sep 2026):
  ZetaS/ChallengeZetaS.lean   Mathlib-only statements: certificates as Props, the headline statements
  ZetaS/Interfaces.lean       GramData, ZeroFrame, GramFamily, FrameFamily, constants, kappaCh
  ZetaS/InterfacesV2.lean     bandwidth-λ interfaces (v2)
  ZetaS/LinAlg/               track L, proved nodes and shared helpers
  ZetaS/SigmaDist/            simple/distinct route, proved nodes
  ZetaS/Window/               track W, the window pipeline and the first end-to-end theorems
  ZetaS/ZeroSide/             zero-side nodes (Z-track) and their shared helpers
  ZetaS/Bandwidth/            bandwidth-λ transfer (KL*), homogeneity, realification
  ZetaS/Majorant/             majorant certificate: explicit majorant, Fourier pair, cells, CertMajV2
  ZetaS/KSide/                track K: first statistic (Theorem G) and simple-or-on-line (SC) route
  ZetaS/Cert/                 track C: the certificate checker v3 (CheckerBase + CheckerLeaves, frozen; bare-name
                              forwarders in ZetaSCertShims/), node definitions, soundness nodes C01–C25, and
                              the chain ChainV3 (`cert_check_sound`, `certAM5_of_checks`, level A)
  ZetaS/Top/                  the top-level assembly: headline theorems of the ζ paper
  ZetaS/Skeleton/             node statements not yet proved (each closed by `sorry`)
A proved node's file lives in its track folder; an unproved one in Skeleton/ (statement-stable swap:
the proved file replaces the skeleton file, statement byte-identical).
This root imports every module, so any clash of public names between modules is caught here.
-/
import ZetaS.Basic
import ZetaS.ChallengeZetaS
import ZetaS.Interfaces
import ZetaS.InterfacesV2
import ZetaS.LinAlg.Helpers
import ZetaS.LinAlg.PhiMHelpers
import ZetaS.LinAlg.SpecHelpers
import ZetaS.LinAlg.L1_StabRankTrace
import ZetaS.LinAlg.L2_StabRankTraceTwo
import ZetaS.LinAlg.L3_PhiM
import ZetaS.LinAlg.L3b_PhiM_props
import ZetaS.LinAlg.L5_PairRemoval
import ZetaS.LinAlg.L6_TraceLipschitz
import ZetaS.LinAlg.L8_NegIndexAdd
import ZetaS.SigmaDist.A1_OnSlackIdentity
import ZetaS.SigmaDist.A1b_BetaBound
import ZetaS.SigmaDist.N3_KernelAntitone
import ZetaS.SigmaDist.C1_ReversalClasses
import ZetaS.SigmaDist.SigmaHelpers
import ZetaS.SigmaDist.A2_AggTrueWindow
import ZetaS.SigmaDist.A8_SigmaDistAbstract
import ZetaS.Window.PolyWindow
import ZetaS.Window.CosWindow
import ZetaS.Window.ProfileMoments
import ZetaS.Window.ProfileAutocorr
import ZetaS.Window.WindowInstances
import ZetaS.Window.WindowLimits
import ZetaS.Window.TracesV
import ZetaS.Window.EndgameV
import ZetaS.Window.HeadlineV
import ZetaS.Window.GramV
import ZetaS.Skeleton.A5_SeparatedRoom
import ZetaS.Skeleton.A7_OLL
import ZetaS.Skeleton.K0_FrameToGram
import ZetaS.Skeleton.K1_LocalToBlock
import ZetaS.Skeleton.K2_Packing
import ZetaS.Skeleton.K3_LocalCertTransfer
import ZetaS.Skeleton.K4_StabFixedT
import ZetaS.Skeleton.K5_TransferMcirc
import ZetaS.Skeleton.K6_ThmG
import ZetaS.Skeleton.K6a_StabConstCont
import ZetaS.Skeleton.K7_SCAbstract
import ZetaS.Skeleton.M1_MajorantKernel
import ZetaS.Skeleton.N1_Numerics
import ZetaS.Skeleton.Hom_Homogeneity
import ZetaS.Skeleton.KL1_BandwidthTransfer
import ZetaS.Skeleton.KL1m_BandwidthTransferAM
import ZetaS.Skeleton.KL2_LamLimit
import ZetaS.Skeleton.KL3_TendstoRlam
import ZetaS.Skeleton.R1_Realify
import ZetaS.Skeleton.W1L_ZetaGramPoly
import ZetaS.Skeleton.W2L_ZetaFrameCos
import ZetaS.Skeleton.W2L_ZetaFramePoly
import ZetaS.Skeleton.Z4_KWinClose
import ZetaS.Skeleton.Z5_KWinDominated
import ZetaS.Skeleton.Z6_Defect
import ZetaS.Skeleton.Z7_PairBlockInertia
import ZetaS.Skeleton.Z9_FrameOfZeroConfig
import ZetaS.LinAlg.CountHelpers
import ZetaS.LinAlg.L7_SchurLocalisation
import ZetaS.LinAlg.L4_Pinching
import ZetaS.ZeroSide.Helpers
import ZetaS.ZeroSide.Z1_GramPoisson
import ZetaS.ZeroSide.Z2_KWinPosDef
import ZetaS.ZeroSide.Z3_OffGridPSD
import ZetaS.ZeroSide.Z8_VHatConj
import ZetaS.Bandwidth.KL1_BandwidthTransfer
import ZetaS.Bandwidth.KL1m_BandwidthTransferAM
import ZetaS.Bandwidth.KL2_LamLimit
import ZetaS.Bandwidth.KL3_TendstoRlam
import ZetaS.Bandwidth.Hom_Homogeneity
import ZetaS.Bandwidth.R1_Realify
import ZetaS.SigmaDist.M1_MajorantKernel
import ZetaS.SigmaDist.A5_SeparatedRoom
import ZetaS.SigmaDist.A6_BlockBounds
import ZetaS.ZeroSide.KWinHelpers
import ZetaS.ZeroSide.Z4_KWinClose
import ZetaS.ZeroSide.Z5_KWinDominated
import ZetaS.ZeroSide.Z6Core
import ZetaS.ZeroSide.Z6_Defect
import ZetaS.ZeroSide.Z6_Defect_fix
import ZetaS.ZeroSide.Z7_PairBlockInertia
import ZetaS.Skeleton.A6_TightChains
import ZetaS.SigmaDist.N2_KPsiThreeQuarters
import ZetaS.SigmaDist.OLLHelpers
import ZetaS.SigmaDist.OLLHeight
import ZetaS.SigmaDist.A7_OLL
import ZetaS.SigmaDist.A6_TightChains
import ZetaS.Majorant.MCert_Majorant
import ZetaS.Majorant.FP_FourierPair
import ZetaS.Majorant.MCert_Cells
import ZetaS.Majorant.CertMajV2
import ZetaS.KSide.KHelpers
import ZetaS.KSide.K1_LocalToBlock
import ZetaS.KSide.K3_LocalCertTransfer
import ZetaS.KSide.K4_StabFixedT
import ZetaS.KSide.K2_Packing
import ZetaS.KSide.K5_TransferMcirc
import ZetaS.KSide.K6a_StabConstCont
import ZetaS.KSide.K6_ThmG
import ZetaS.KSide.K0_FrameToGram
import ZetaS.KSide.K7aux
import ZetaS.KSide.K7_SCAbstract
import ZetaS.ZeroSide.Z9s_Spec
import ZetaS.ZeroSide.Z9a1_OnLineSort
import ZetaS.ZeroSide.Z9a2_OffBlock
import ZetaS.ZeroSide.Z9a3_HatDecomp
import ZetaS.ZeroSide.Z9a4_Frame
import ZetaS.ZeroSide.Z9a6_Counts
import ZetaS.ZeroSide.Z9a5_FrameSpec
import ZetaS.ZeroSide.Z9a_FrameAt
import ZetaS.ZeroSide.Z9b0_Asymp
import ZetaS.ZeroSide.Z9b_TailTransfer
import ZetaS.ZeroSide.Z9c_JIdentity
import ZetaS.ZeroSide.Z9d_Span
import ZetaS.ZeroSide.Z9e_Seams
import ZetaS.ZeroSide.ZetaSeams
import ZetaS.ZeroSide.Z9_FrameOfZeroConfig_fix
import ZetaS.ZeroSide.Z9_FrameOfZeroConfig
import ZetaS.Window.W2L_ZetaFrameCos
import ZetaS.Window.W2L_ZetaFramePoly_fix
import ZetaS.Window.W2L_ZetaFramePoly
import ZetaS.Top.TopDefs
import ZetaS.Cert.CheckerBase
import ZetaS.Cert.CheckerLeaves
import ZetaS.Cert.CheckerCoreV3
import ZetaS.Cert.CertSpecAM5
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C01_QIRound
import ZetaS.Cert.C02_QIOps
import ZetaS.Cert.C03_Horner
import ZetaS.Cert.C04_PiEncl
import ZetaS.Cert.C05_SinCosTaylor
import ZetaS.Cert.C06_SinCosPi
import ZetaS.Cert.C22_ShardAssembly
import ZetaS.Majorant.MajCheck
import ZetaS.Majorant.MajSoundNPos
import ZetaS.Majorant.MajSoundNMaj
import ZetaS.Majorant.Shards.NPosS0
import ZetaS.Majorant.Shards.NPosS1
import ZetaS.Majorant.Shards.NPosS2
import ZetaS.Majorant.Shards.NPosS3
import ZetaS.Majorant.Shards.NPosS4
import ZetaS.Majorant.Shards.NPosS5
import ZetaS.Majorant.Shards.NPosS6
import ZetaS.Majorant.Shards.NPosS7
import ZetaS.Majorant.Shards.NPosS8
import ZetaS.Majorant.Shards.NPosS9
import ZetaS.Majorant.Shards.NPosS10
import ZetaS.Majorant.Shards.NPosS11
import ZetaS.Majorant.Shards.NMajS0
import ZetaS.Majorant.NPosProof
import ZetaS.Majorant.CertMajV2Proof
import ZetaS.KSide.K0_FrameToGramHEq
import ZetaS.Top.PolyMoments
import ZetaS.Top.N1_Numerics
import ZetaS.Top.N2_Robust
import ZetaS.Skeleton.A8g_SigmaDistGeneral
import ZetaS.Top.A8K
import ZetaS.Top.OLLHeight5
import ZetaS.Top.A7K5
import ZetaS.Top.A7K7b
import ZetaS.Top.TopSolution
import ZetaS.Window.W1L_ZetaGramPoly
import ZetaS.Top.TopSSC
import ZetaS.Top.KPsiCos
import ZetaS.Top.TopFinal
import ZetaS.Cert.C07a_SincDeriv
import ZetaS.Cert.C07b_SincEncl
import ZetaS.Cert.C08_KCosDerivs
import ZetaS.Cert.C09_KEncl
import ZetaS.Cert.C14_Taylor2Minorant
import ZetaS.Cert.C15_ChordMinorant
import ZetaS.Cert.C16_TangentLine
import ZetaS.Cert.C17_CapLeaf
import ZetaS.Cert.C19a_PsdLDL
import ZetaS.Skeleton.C10_KCosD3
import ZetaS.Skeleton.C11_TaylorModel
import ZetaS.Skeleton.C12_CellSound
import ZetaS.Skeleton.C13_SpanBounds
import ZetaS.Skeleton.C19b_CvxLeaf
import ZetaS.Skeleton.C23_KPsiCos
import ZetaS.Skeleton.C24_W5Fields
import ZetaS.Skeleton.C25_ClassBridge
import ZetaS.Cert.C23_KPsiCos
import ZetaS.Cert.C24_W5Fields
import ZetaS.Cert.C25_ClassBridge
import ZetaS.Cert.C10_KCosD3
import ZetaS.Cert.CheckerTestsV3
import ZetaS.Cert.C11_TaylorModel
import ZetaS.Cert.C12_CellSound
import ZetaS.Cert.C13_SpanBounds
import ZetaS.Cert.C18_LPLeaf
import ZetaS.Cert.C19b_CvxLeaf
import ZetaS.Cert.C20_NodeSound
import ZetaS.Cert.C21_CertSound
import ZetaS.Cert.ChainV3
import ZetaS.Top.TopSolutionGeneral
import ZetaS.Majorant.CertMajProof
