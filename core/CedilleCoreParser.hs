{-# OPTIONS_GHC -w #-}
module CedilleCoreParser where

import CedilleCoreTypes
import CedilleCoreToString
import CedilleCoreLexer hiding (main)

import Control.Monad
import System.Environment
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.19.5

data HappyAbsSyn 
	= HappyTerminal (Token)
	| HappyErrorToken Int
	| HappyAbsSyn8 (Cmds)
	| HappyAbsSyn9 (Cmd)
	| HappyAbsSyn10 (Term)
	| HappyAbsSyn14 (PureTerm)
	| HappyAbsSyn17 (Type)
	| HappyAbsSyn20 (PureType)
	| HappyAbsSyn23 (Kind)
	| HappyAbsSyn24 (PureKind)
	| HappyAbsSyn25 (Tk)
	| HappyAbsSyn26 (PureTk)
	| HappyAbsSyn27 (Token)

{- to allow type-synonyms as our monads (likely
 - with explicitly-specified bind and return)
 - in Haskell98, it seems that with
 - /type M a = .../, then /(HappyReduction M)/
 - is not allowed.  But Happy is a
 - code-generator that can just substitute it.
type HappyReduction m = 
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> m HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> m HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> m HappyAbsSyn
-}

action_0,
 action_1,
 action_2,
 action_3,
 action_4,
 action_5,
 action_6,
 action_7,
 action_8,
 action_9,
 action_10,
 action_11,
 action_12,
 action_13,
 action_14,
 action_15,
 action_16,
 action_17,
 action_18,
 action_19,
 action_20,
 action_21,
 action_22,
 action_23,
 action_24,
 action_25,
 action_26,
 action_27,
 action_28,
 action_29,
 action_30,
 action_31,
 action_32,
 action_33,
 action_34,
 action_35,
 action_36,
 action_37,
 action_38,
 action_39,
 action_40,
 action_41,
 action_42,
 action_43,
 action_44,
 action_45,
 action_46,
 action_47,
 action_48,
 action_49,
 action_50,
 action_51,
 action_52,
 action_53,
 action_54,
 action_55,
 action_56,
 action_57,
 action_58,
 action_59,
 action_60,
 action_61,
 action_62,
 action_63,
 action_64,
 action_65,
 action_66,
 action_67,
 action_68,
 action_69,
 action_70,
 action_71,
 action_72,
 action_73,
 action_74,
 action_75,
 action_76,
 action_77,
 action_78,
 action_79,
 action_80,
 action_81,
 action_82,
 action_83,
 action_84,
 action_85,
 action_86,
 action_87,
 action_88,
 action_89,
 action_90,
 action_91,
 action_92,
 action_93,
 action_94,
 action_95,
 action_96,
 action_97,
 action_98,
 action_99,
 action_100,
 action_101,
 action_102,
 action_103,
 action_104,
 action_105,
 action_106,
 action_107,
 action_108,
 action_109,
 action_110,
 action_111,
 action_112,
 action_113,
 action_114,
 action_115,
 action_116,
 action_117,
 action_118,
 action_119,
 action_120,
 action_121,
 action_122,
 action_123,
 action_124,
 action_125,
 action_126,
 action_127,
 action_128,
 action_129,
 action_130,
 action_131,
 action_132,
 action_133,
 action_134,
 action_135,
 action_136,
 action_137,
 action_138,
 action_139,
 action_140,
 action_141,
 action_142,
 action_143,
 action_144,
 action_145,
 action_146,
 action_147,
 action_148,
 action_149,
 action_150,
 action_151,
 action_152,
 action_153,
 action_154,
 action_155,
 action_156,
 action_157,
 action_158,
 action_159,
 action_160,
 action_161,
 action_162,
 action_163,
 action_164,
 action_165,
 action_166,
 action_167,
 action_168,
 action_169,
 action_170,
 action_171,
 action_172,
 action_173,
 action_174,
 action_175,
 action_176,
 action_177,
 action_178,
 action_179,
 action_180,
 action_181,
 action_182,
 action_183,
 action_184,
 action_185,
 action_186,
 action_187,
 action_188,
 action_189,
 action_190,
 action_191,
 action_192,
 action_193,
 action_194,
 action_195 :: () => Int -> ({-HappyReduction (Alex) = -}
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> (Alex) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> (Alex) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> (Alex) HappyAbsSyn)

happyReduce_5,
 happyReduce_6,
 happyReduce_7,
 happyReduce_8,
 happyReduce_9,
 happyReduce_10,
 happyReduce_11,
 happyReduce_12,
 happyReduce_13,
 happyReduce_14,
 happyReduce_15,
 happyReduce_16,
 happyReduce_17,
 happyReduce_18,
 happyReduce_19,
 happyReduce_20,
 happyReduce_21,
 happyReduce_22,
 happyReduce_23,
 happyReduce_24,
 happyReduce_25,
 happyReduce_26,
 happyReduce_27,
 happyReduce_28,
 happyReduce_29,
 happyReduce_30,
 happyReduce_31,
 happyReduce_32,
 happyReduce_33,
 happyReduce_34,
 happyReduce_35,
 happyReduce_36,
 happyReduce_37,
 happyReduce_38,
 happyReduce_39,
 happyReduce_40,
 happyReduce_41,
 happyReduce_42,
 happyReduce_43,
 happyReduce_44,
 happyReduce_45,
 happyReduce_46,
 happyReduce_47,
 happyReduce_48,
 happyReduce_49,
 happyReduce_50,
 happyReduce_51,
 happyReduce_52,
 happyReduce_53,
 happyReduce_54,
 happyReduce_55,
 happyReduce_56,
 happyReduce_57,
 happyReduce_58,
 happyReduce_59,
 happyReduce_60,
 happyReduce_61,
 happyReduce_62,
 happyReduce_63,
 happyReduce_64,
 happyReduce_65 :: () => ({-HappyReduction (Alex) = -}
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> (Alex) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> (Alex) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> (Alex) HappyAbsSyn)

action_0 (28) = happyShift action_35
action_0 (8) = happyGoto action_36
action_0 (9) = happyGoto action_37
action_0 _ = happyReduce_5

action_1 (28) = happyShift action_35
action_1 (9) = happyGoto action_34
action_1 _ = happyFail

action_2 (28) = happyShift action_27
action_2 (34) = happyShift action_28
action_2 (39) = happyShift action_29
action_2 (42) = happyShift action_30
action_2 (44) = happyShift action_31
action_2 (45) = happyShift action_32
action_2 (47) = happyShift action_33
action_2 (17) = happyGoto action_24
action_2 (18) = happyGoto action_25
action_2 (19) = happyGoto action_26
action_2 _ = happyFail

action_3 (28) = happyShift action_14
action_3 (34) = happyShift action_15
action_3 (36) = happyShift action_16
action_3 (45) = happyShift action_17
action_3 (46) = happyShift action_18
action_3 (48) = happyShift action_19
action_3 (49) = happyShift action_20
action_3 (52) = happyShift action_21
action_3 (53) = happyShift action_22
action_3 (54) = happyShift action_23
action_3 (10) = happyGoto action_10
action_3 (11) = happyGoto action_11
action_3 (12) = happyGoto action_12
action_3 (13) = happyGoto action_13
action_3 _ = happyFail

action_4 (34) = happyShift action_7
action_4 (43) = happyShift action_8
action_4 (56) = happyShift action_9
action_4 (23) = happyGoto action_6
action_4 _ = happyFail

action_5 _ = happyFail

action_6 (58) = happyAccept
action_6 _ = happyFail

action_7 (34) = happyShift action_7
action_7 (43) = happyShift action_8
action_7 (56) = happyShift action_9
action_7 (23) = happyGoto action_79
action_7 _ = happyFail

action_8 (28) = happyShift action_42
action_8 (30) = happyShift action_43
action_8 (27) = happyGoto action_78
action_8 _ = happyFail

action_9 _ = happyReduce_55

action_10 (58) = happyAccept
action_10 _ = happyFail

action_11 (28) = happyShift action_14
action_11 (34) = happyShift action_15
action_11 (36) = happyShift action_16
action_11 (48) = happyShift action_19
action_11 (50) = happyShift action_76
action_11 (51) = happyShift action_77
action_11 (13) = happyGoto action_75
action_11 _ = happyReduce_14

action_12 _ = happyReduce_18

action_13 (29) = happyShift action_74
action_13 _ = happyReduce_20

action_14 _ = happyReduce_21

action_15 (28) = happyShift action_14
action_15 (34) = happyShift action_15
action_15 (36) = happyShift action_16
action_15 (45) = happyShift action_17
action_15 (46) = happyShift action_18
action_15 (48) = happyShift action_19
action_15 (49) = happyShift action_20
action_15 (52) = happyShift action_21
action_15 (53) = happyShift action_22
action_15 (54) = happyShift action_23
action_15 (10) = happyGoto action_73
action_15 (11) = happyGoto action_11
action_15 (12) = happyGoto action_12
action_15 (13) = happyGoto action_13
action_15 _ = happyFail

action_16 (28) = happyShift action_14
action_16 (34) = happyShift action_15
action_16 (36) = happyShift action_16
action_16 (45) = happyShift action_17
action_16 (46) = happyShift action_18
action_16 (48) = happyShift action_19
action_16 (49) = happyShift action_20
action_16 (52) = happyShift action_21
action_16 (53) = happyShift action_22
action_16 (54) = happyShift action_23
action_16 (10) = happyGoto action_72
action_16 (11) = happyGoto action_11
action_16 (12) = happyGoto action_12
action_16 (13) = happyGoto action_13
action_16 _ = happyFail

action_17 (28) = happyShift action_42
action_17 (30) = happyShift action_43
action_17 (27) = happyGoto action_71
action_17 _ = happyFail

action_18 (28) = happyShift action_42
action_18 (30) = happyShift action_43
action_18 (27) = happyGoto action_70
action_18 _ = happyFail

action_19 (28) = happyShift action_50
action_19 (34) = happyShift action_51
action_19 (16) = happyGoto action_69
action_19 _ = happyFail

action_20 (28) = happyShift action_62
action_20 (34) = happyShift action_63
action_20 (39) = happyShift action_64
action_20 (42) = happyShift action_65
action_20 (44) = happyShift action_66
action_20 (45) = happyShift action_67
action_20 (47) = happyShift action_68
action_20 (20) = happyGoto action_59
action_20 (21) = happyGoto action_60
action_20 (22) = happyGoto action_61
action_20 _ = happyFail

action_21 (28) = happyShift action_14
action_21 (34) = happyShift action_15
action_21 (36) = happyShift action_16
action_21 (48) = happyShift action_19
action_21 (52) = happyShift action_21
action_21 (12) = happyGoto action_58
action_21 (13) = happyGoto action_13
action_21 _ = happyFail

action_22 (28) = happyShift action_14
action_22 (34) = happyShift action_15
action_22 (36) = happyShift action_16
action_22 (48) = happyShift action_19
action_22 (52) = happyShift action_21
action_22 (12) = happyGoto action_57
action_22 (13) = happyGoto action_13
action_22 _ = happyFail

action_23 (28) = happyShift action_14
action_23 (34) = happyShift action_15
action_23 (36) = happyShift action_16
action_23 (48) = happyShift action_19
action_23 (52) = happyShift action_21
action_23 (12) = happyGoto action_56
action_23 (13) = happyGoto action_13
action_23 _ = happyFail

action_24 (58) = happyAccept
action_24 _ = happyFail

action_25 (28) = happyShift action_14
action_25 (34) = happyShift action_15
action_25 (36) = happyShift action_16
action_25 (48) = happyShift action_19
action_25 (50) = happyShift action_55
action_25 (13) = happyGoto action_54
action_25 _ = happyReduce_36

action_26 _ = happyReduce_39

action_27 _ = happyReduce_40

action_28 (28) = happyShift action_27
action_28 (34) = happyShift action_28
action_28 (39) = happyShift action_29
action_28 (42) = happyShift action_30
action_28 (44) = happyShift action_31
action_28 (45) = happyShift action_32
action_28 (47) = happyShift action_33
action_28 (17) = happyGoto action_53
action_28 (18) = happyGoto action_25
action_28 (19) = happyGoto action_26
action_28 _ = happyFail

action_29 (28) = happyShift action_50
action_29 (34) = happyShift action_51
action_29 (45) = happyShift action_52
action_29 (14) = happyGoto action_47
action_29 (15) = happyGoto action_48
action_29 (16) = happyGoto action_49
action_29 _ = happyFail

action_30 (28) = happyShift action_42
action_30 (30) = happyShift action_43
action_30 (27) = happyGoto action_46
action_30 _ = happyFail

action_31 (28) = happyShift action_42
action_31 (30) = happyShift action_43
action_31 (27) = happyGoto action_45
action_31 _ = happyFail

action_32 (28) = happyShift action_42
action_32 (30) = happyShift action_43
action_32 (27) = happyGoto action_44
action_32 _ = happyFail

action_33 (28) = happyShift action_42
action_33 (30) = happyShift action_43
action_33 (27) = happyGoto action_41
action_33 _ = happyFail

action_34 (58) = happyAccept
action_34 _ = happyFail

action_35 (31) = happyShift action_39
action_35 (32) = happyShift action_40
action_35 _ = happyFail

action_36 (58) = happyAccept
action_36 _ = happyFail

action_37 (28) = happyShift action_35
action_37 (8) = happyGoto action_38
action_37 (9) = happyGoto action_37
action_37 _ = happyReduce_5

action_38 _ = happyReduce_6

action_39 (28) = happyShift action_14
action_39 (34) = happyShift action_15
action_39 (36) = happyShift action_16
action_39 (45) = happyShift action_17
action_39 (46) = happyShift action_18
action_39 (48) = happyShift action_19
action_39 (49) = happyShift action_20
action_39 (52) = happyShift action_21
action_39 (53) = happyShift action_22
action_39 (54) = happyShift action_23
action_39 (10) = happyGoto action_111
action_39 (11) = happyGoto action_11
action_39 (12) = happyGoto action_12
action_39 (13) = happyGoto action_13
action_39 _ = happyFail

action_40 (31) = happyShift action_110
action_40 _ = happyFail

action_41 (41) = happyShift action_109
action_41 _ = happyFail

action_42 _ = happyReduce_65

action_43 _ = happyReduce_64

action_44 (41) = happyShift action_108
action_44 _ = happyFail

action_45 (41) = happyShift action_107
action_45 _ = happyFail

action_46 (41) = happyShift action_106
action_46 _ = happyFail

action_47 (55) = happyShift action_105
action_47 _ = happyFail

action_48 (28) = happyShift action_50
action_48 (34) = happyShift action_51
action_48 (16) = happyGoto action_104
action_48 _ = happyReduce_27

action_49 _ = happyReduce_29

action_50 _ = happyReduce_30

action_51 (28) = happyShift action_50
action_51 (34) = happyShift action_51
action_51 (45) = happyShift action_52
action_51 (14) = happyGoto action_103
action_51 (15) = happyGoto action_48
action_51 (16) = happyGoto action_49
action_51 _ = happyFail

action_52 (28) = happyShift action_42
action_52 (30) = happyShift action_43
action_52 (27) = happyGoto action_102
action_52 _ = happyFail

action_53 (35) = happyShift action_101
action_53 _ = happyFail

action_54 (29) = happyShift action_74
action_54 _ = happyReduce_38

action_55 (28) = happyShift action_27
action_55 (34) = happyShift action_28
action_55 (39) = happyShift action_29
action_55 (19) = happyGoto action_100
action_55 _ = happyFail

action_56 (51) = happyShift action_99
action_56 _ = happyFail

action_57 (57) = happyShift action_98
action_57 _ = happyFail

action_58 _ = happyReduce_19

action_59 (51) = happyShift action_97
action_59 _ = happyFail

action_60 (28) = happyShift action_50
action_60 (34) = happyShift action_51
action_60 (50) = happyShift action_96
action_60 (16) = happyGoto action_95
action_60 _ = happyReduce_47

action_61 _ = happyReduce_50

action_62 _ = happyReduce_51

action_63 (28) = happyShift action_62
action_63 (34) = happyShift action_63
action_63 (39) = happyShift action_64
action_63 (42) = happyShift action_65
action_63 (44) = happyShift action_66
action_63 (45) = happyShift action_67
action_63 (47) = happyShift action_68
action_63 (20) = happyGoto action_94
action_63 (21) = happyGoto action_60
action_63 (22) = happyGoto action_61
action_63 _ = happyFail

action_64 (28) = happyShift action_50
action_64 (34) = happyShift action_51
action_64 (45) = happyShift action_52
action_64 (14) = happyGoto action_93
action_64 (15) = happyGoto action_48
action_64 (16) = happyGoto action_49
action_64 _ = happyFail

action_65 (28) = happyShift action_42
action_65 (30) = happyShift action_43
action_65 (27) = happyGoto action_92
action_65 _ = happyFail

action_66 (28) = happyShift action_42
action_66 (30) = happyShift action_43
action_66 (27) = happyGoto action_91
action_66 _ = happyFail

action_67 (28) = happyShift action_42
action_67 (30) = happyShift action_43
action_67 (27) = happyGoto action_90
action_67 _ = happyFail

action_68 (28) = happyShift action_42
action_68 (30) = happyShift action_43
action_68 (27) = happyGoto action_89
action_68 _ = happyFail

action_69 (39) = happyShift action_88
action_69 _ = happyFail

action_70 (41) = happyShift action_87
action_70 _ = happyFail

action_71 (41) = happyShift action_86
action_71 _ = happyFail

action_72 (38) = happyShift action_85
action_72 _ = happyFail

action_73 (35) = happyShift action_84
action_73 _ = happyFail

action_74 _ = happyReduce_24

action_75 (29) = happyShift action_74
action_75 _ = happyReduce_15

action_76 (28) = happyShift action_27
action_76 (34) = happyShift action_28
action_76 (39) = happyShift action_29
action_76 (19) = happyGoto action_83
action_76 _ = happyFail

action_77 (28) = happyShift action_14
action_77 (34) = happyShift action_15
action_77 (36) = happyShift action_16
action_77 (48) = happyShift action_19
action_77 (13) = happyGoto action_82
action_77 _ = happyFail

action_78 (41) = happyShift action_81
action_78 _ = happyFail

action_79 (35) = happyShift action_80
action_79 _ = happyFail

action_80 _ = happyReduce_56

action_81 (28) = happyShift action_27
action_81 (34) = happyShift action_118
action_81 (39) = happyShift action_29
action_81 (42) = happyShift action_30
action_81 (43) = happyShift action_8
action_81 (44) = happyShift action_31
action_81 (45) = happyShift action_32
action_81 (47) = happyShift action_33
action_81 (56) = happyShift action_9
action_81 (17) = happyGoto action_115
action_81 (18) = happyGoto action_25
action_81 (19) = happyGoto action_26
action_81 (23) = happyGoto action_116
action_81 (25) = happyGoto action_138
action_81 _ = happyFail

action_82 (29) = happyShift action_74
action_82 _ = happyReduce_16

action_83 _ = happyReduce_17

action_84 _ = happyReduce_25

action_85 (28) = happyShift action_14
action_85 (34) = happyShift action_15
action_85 (36) = happyShift action_16
action_85 (45) = happyShift action_17
action_85 (46) = happyShift action_18
action_85 (48) = happyShift action_19
action_85 (49) = happyShift action_20
action_85 (52) = happyShift action_21
action_85 (53) = happyShift action_22
action_85 (54) = happyShift action_23
action_85 (10) = happyGoto action_137
action_85 (11) = happyGoto action_11
action_85 (12) = happyGoto action_12
action_85 (13) = happyGoto action_13
action_85 _ = happyFail

action_86 (28) = happyShift action_27
action_86 (34) = happyShift action_28
action_86 (39) = happyShift action_29
action_86 (42) = happyShift action_30
action_86 (44) = happyShift action_31
action_86 (45) = happyShift action_32
action_86 (47) = happyShift action_33
action_86 (17) = happyGoto action_136
action_86 (18) = happyGoto action_25
action_86 (19) = happyGoto action_26
action_86 _ = happyFail

action_87 (28) = happyShift action_27
action_87 (34) = happyShift action_118
action_87 (39) = happyShift action_29
action_87 (42) = happyShift action_30
action_87 (43) = happyShift action_8
action_87 (44) = happyShift action_31
action_87 (45) = happyShift action_32
action_87 (47) = happyShift action_33
action_87 (56) = happyShift action_9
action_87 (17) = happyGoto action_115
action_87 (18) = happyGoto action_25
action_87 (19) = happyGoto action_26
action_87 (23) = happyGoto action_116
action_87 (25) = happyGoto action_135
action_87 _ = happyFail

action_88 (28) = happyShift action_50
action_88 (34) = happyShift action_51
action_88 (45) = happyShift action_52
action_88 (14) = happyGoto action_134
action_88 (15) = happyGoto action_48
action_88 (16) = happyGoto action_49
action_88 _ = happyFail

action_89 (41) = happyShift action_133
action_89 _ = happyFail

action_90 (41) = happyShift action_132
action_90 _ = happyFail

action_91 (41) = happyShift action_131
action_91 _ = happyFail

action_92 (41) = happyShift action_130
action_92 _ = happyFail

action_93 (55) = happyShift action_129
action_93 _ = happyFail

action_94 (35) = happyShift action_128
action_94 _ = happyFail

action_95 _ = happyReduce_49

action_96 (28) = happyShift action_62
action_96 (34) = happyShift action_63
action_96 (39) = happyShift action_64
action_96 (22) = happyGoto action_127
action_96 _ = happyFail

action_97 (28) = happyShift action_14
action_97 (34) = happyShift action_15
action_97 (36) = happyShift action_16
action_97 (45) = happyShift action_17
action_97 (46) = happyShift action_18
action_97 (48) = happyShift action_19
action_97 (49) = happyShift action_20
action_97 (52) = happyShift action_21
action_97 (53) = happyShift action_22
action_97 (54) = happyShift action_23
action_97 (10) = happyGoto action_126
action_97 (11) = happyGoto action_11
action_97 (12) = happyGoto action_12
action_97 (13) = happyGoto action_13
action_97 _ = happyFail

action_98 (28) = happyShift action_125
action_98 _ = happyFail

action_99 (28) = happyShift action_14
action_99 (34) = happyShift action_15
action_99 (36) = happyShift action_16
action_99 (45) = happyShift action_17
action_99 (46) = happyShift action_18
action_99 (48) = happyShift action_19
action_99 (49) = happyShift action_20
action_99 (52) = happyShift action_21
action_99 (53) = happyShift action_22
action_99 (54) = happyShift action_23
action_99 (10) = happyGoto action_124
action_99 (11) = happyGoto action_11
action_99 (12) = happyGoto action_12
action_99 (13) = happyGoto action_13
action_99 _ = happyFail

action_100 _ = happyReduce_37

action_101 _ = happyReduce_42

action_102 (33) = happyShift action_123
action_102 _ = happyFail

action_103 (35) = happyShift action_122
action_103 _ = happyFail

action_104 _ = happyReduce_28

action_105 (28) = happyShift action_50
action_105 (34) = happyShift action_51
action_105 (45) = happyShift action_52
action_105 (14) = happyGoto action_121
action_105 (15) = happyGoto action_48
action_105 (16) = happyGoto action_49
action_105 _ = happyFail

action_106 (28) = happyShift action_27
action_106 (34) = happyShift action_28
action_106 (39) = happyShift action_29
action_106 (42) = happyShift action_30
action_106 (44) = happyShift action_31
action_106 (45) = happyShift action_32
action_106 (47) = happyShift action_33
action_106 (17) = happyGoto action_120
action_106 (18) = happyGoto action_25
action_106 (19) = happyGoto action_26
action_106 _ = happyFail

action_107 (28) = happyShift action_27
action_107 (34) = happyShift action_118
action_107 (39) = happyShift action_29
action_107 (42) = happyShift action_30
action_107 (43) = happyShift action_8
action_107 (44) = happyShift action_31
action_107 (45) = happyShift action_32
action_107 (47) = happyShift action_33
action_107 (56) = happyShift action_9
action_107 (17) = happyGoto action_115
action_107 (18) = happyGoto action_25
action_107 (19) = happyGoto action_26
action_107 (23) = happyGoto action_116
action_107 (25) = happyGoto action_119
action_107 _ = happyFail

action_108 (28) = happyShift action_27
action_108 (34) = happyShift action_118
action_108 (39) = happyShift action_29
action_108 (42) = happyShift action_30
action_108 (43) = happyShift action_8
action_108 (44) = happyShift action_31
action_108 (45) = happyShift action_32
action_108 (47) = happyShift action_33
action_108 (56) = happyShift action_9
action_108 (17) = happyGoto action_115
action_108 (18) = happyGoto action_25
action_108 (19) = happyGoto action_26
action_108 (23) = happyGoto action_116
action_108 (25) = happyGoto action_117
action_108 _ = happyFail

action_109 (28) = happyShift action_27
action_109 (34) = happyShift action_28
action_109 (39) = happyShift action_29
action_109 (42) = happyShift action_30
action_109 (44) = happyShift action_31
action_109 (45) = happyShift action_32
action_109 (47) = happyShift action_33
action_109 (17) = happyGoto action_114
action_109 (18) = happyGoto action_25
action_109 (19) = happyGoto action_26
action_109 _ = happyFail

action_110 (28) = happyShift action_27
action_110 (34) = happyShift action_28
action_110 (39) = happyShift action_29
action_110 (42) = happyShift action_30
action_110 (44) = happyShift action_31
action_110 (45) = happyShift action_32
action_110 (47) = happyShift action_33
action_110 (17) = happyGoto action_113
action_110 (18) = happyGoto action_25
action_110 (19) = happyGoto action_26
action_110 _ = happyFail

action_111 (33) = happyShift action_112
action_111 _ = happyFail

action_112 _ = happyReduce_7

action_113 (33) = happyShift action_162
action_113 _ = happyFail

action_114 (33) = happyShift action_161
action_114 _ = happyFail

action_115 _ = happyReduce_60

action_116 _ = happyReduce_61

action_117 (33) = happyShift action_160
action_117 _ = happyFail

action_118 (28) = happyShift action_27
action_118 (34) = happyShift action_118
action_118 (39) = happyShift action_29
action_118 (42) = happyShift action_30
action_118 (43) = happyShift action_8
action_118 (44) = happyShift action_31
action_118 (45) = happyShift action_32
action_118 (47) = happyShift action_33
action_118 (56) = happyShift action_9
action_118 (17) = happyGoto action_53
action_118 (18) = happyGoto action_25
action_118 (19) = happyGoto action_26
action_118 (23) = happyGoto action_79
action_118 _ = happyFail

action_119 (33) = happyShift action_159
action_119 _ = happyFail

action_120 (33) = happyShift action_158
action_120 _ = happyFail

action_121 (40) = happyShift action_157
action_121 _ = happyFail

action_122 _ = happyReduce_31

action_123 (28) = happyShift action_50
action_123 (34) = happyShift action_51
action_123 (45) = happyShift action_52
action_123 (14) = happyGoto action_156
action_123 (15) = happyGoto action_48
action_123 (16) = happyGoto action_49
action_123 _ = happyFail

action_124 (39) = happyShift action_155
action_124 _ = happyFail

action_125 (33) = happyShift action_154
action_125 _ = happyFail

action_126 _ = happyReduce_13

action_127 _ = happyReduce_48

action_128 _ = happyReduce_53

action_129 (28) = happyShift action_50
action_129 (34) = happyShift action_51
action_129 (45) = happyShift action_52
action_129 (14) = happyGoto action_153
action_129 (15) = happyGoto action_48
action_129 (16) = happyGoto action_49
action_129 _ = happyFail

action_130 (28) = happyShift action_62
action_130 (34) = happyShift action_63
action_130 (39) = happyShift action_64
action_130 (42) = happyShift action_65
action_130 (44) = happyShift action_66
action_130 (45) = happyShift action_67
action_130 (47) = happyShift action_68
action_130 (20) = happyGoto action_152
action_130 (21) = happyGoto action_60
action_130 (22) = happyGoto action_61
action_130 _ = happyFail

action_131 (28) = happyShift action_62
action_131 (34) = happyShift action_148
action_131 (39) = happyShift action_64
action_131 (42) = happyShift action_65
action_131 (43) = happyShift action_149
action_131 (44) = happyShift action_66
action_131 (45) = happyShift action_67
action_131 (47) = happyShift action_68
action_131 (56) = happyShift action_150
action_131 (20) = happyGoto action_145
action_131 (21) = happyGoto action_60
action_131 (22) = happyGoto action_61
action_131 (24) = happyGoto action_146
action_131 (26) = happyGoto action_151
action_131 _ = happyFail

action_132 (28) = happyShift action_62
action_132 (34) = happyShift action_148
action_132 (39) = happyShift action_64
action_132 (42) = happyShift action_65
action_132 (43) = happyShift action_149
action_132 (44) = happyShift action_66
action_132 (45) = happyShift action_67
action_132 (47) = happyShift action_68
action_132 (56) = happyShift action_150
action_132 (20) = happyGoto action_145
action_132 (21) = happyGoto action_60
action_132 (22) = happyGoto action_61
action_132 (24) = happyGoto action_146
action_132 (26) = happyGoto action_147
action_132 _ = happyFail

action_133 (28) = happyShift action_62
action_133 (34) = happyShift action_63
action_133 (39) = happyShift action_64
action_133 (42) = happyShift action_65
action_133 (44) = happyShift action_66
action_133 (45) = happyShift action_67
action_133 (47) = happyShift action_68
action_133 (20) = happyGoto action_144
action_133 (21) = happyGoto action_60
action_133 (22) = happyGoto action_61
action_133 _ = happyFail

action_134 (40) = happyShift action_143
action_134 _ = happyFail

action_135 (33) = happyShift action_142
action_135 _ = happyFail

action_136 (33) = happyShift action_141
action_136 _ = happyFail

action_137 (57) = happyShift action_140
action_137 _ = happyFail

action_138 (33) = happyShift action_139
action_138 _ = happyFail

action_139 (34) = happyShift action_7
action_139 (43) = happyShift action_8
action_139 (56) = happyShift action_9
action_139 (23) = happyGoto action_179
action_139 _ = happyFail

action_140 (28) = happyShift action_178
action_140 _ = happyFail

action_141 (28) = happyShift action_14
action_141 (34) = happyShift action_15
action_141 (36) = happyShift action_16
action_141 (45) = happyShift action_17
action_141 (46) = happyShift action_18
action_141 (48) = happyShift action_19
action_141 (49) = happyShift action_20
action_141 (52) = happyShift action_21
action_141 (53) = happyShift action_22
action_141 (54) = happyShift action_23
action_141 (10) = happyGoto action_177
action_141 (11) = happyGoto action_11
action_141 (12) = happyGoto action_12
action_141 (13) = happyGoto action_13
action_141 _ = happyFail

action_142 (28) = happyShift action_14
action_142 (34) = happyShift action_15
action_142 (36) = happyShift action_16
action_142 (45) = happyShift action_17
action_142 (46) = happyShift action_18
action_142 (48) = happyShift action_19
action_142 (49) = happyShift action_20
action_142 (52) = happyShift action_21
action_142 (53) = happyShift action_22
action_142 (54) = happyShift action_23
action_142 (10) = happyGoto action_176
action_142 (11) = happyGoto action_11
action_142 (12) = happyGoto action_12
action_142 (13) = happyGoto action_13
action_142 _ = happyFail

action_143 _ = happyReduce_22

action_144 (33) = happyShift action_175
action_144 _ = happyFail

action_145 _ = happyReduce_62

action_146 _ = happyReduce_63

action_147 (33) = happyShift action_174
action_147 _ = happyFail

action_148 (28) = happyShift action_62
action_148 (34) = happyShift action_148
action_148 (39) = happyShift action_64
action_148 (42) = happyShift action_65
action_148 (43) = happyShift action_149
action_148 (44) = happyShift action_66
action_148 (45) = happyShift action_67
action_148 (47) = happyShift action_68
action_148 (56) = happyShift action_150
action_148 (20) = happyGoto action_94
action_148 (21) = happyGoto action_60
action_148 (22) = happyGoto action_61
action_148 (24) = happyGoto action_173
action_148 _ = happyFail

action_149 (28) = happyShift action_42
action_149 (30) = happyShift action_43
action_149 (27) = happyGoto action_172
action_149 _ = happyFail

action_150 _ = happyReduce_58

action_151 (33) = happyShift action_171
action_151 _ = happyFail

action_152 (33) = happyShift action_170
action_152 _ = happyFail

action_153 (40) = happyShift action_169
action_153 _ = happyFail

action_154 (28) = happyShift action_62
action_154 (34) = happyShift action_63
action_154 (39) = happyShift action_64
action_154 (42) = happyShift action_65
action_154 (44) = happyShift action_66
action_154 (45) = happyShift action_67
action_154 (47) = happyShift action_68
action_154 (20) = happyGoto action_168
action_154 (21) = happyGoto action_60
action_154 (22) = happyGoto action_61
action_154 _ = happyFail

action_155 (28) = happyShift action_50
action_155 (34) = happyShift action_51
action_155 (45) = happyShift action_52
action_155 (14) = happyGoto action_167
action_155 (15) = happyGoto action_48
action_155 (16) = happyGoto action_49
action_155 _ = happyFail

action_156 _ = happyReduce_26

action_157 _ = happyReduce_41

action_158 (28) = happyShift action_27
action_158 (34) = happyShift action_28
action_158 (39) = happyShift action_29
action_158 (42) = happyShift action_30
action_158 (44) = happyShift action_31
action_158 (45) = happyShift action_32
action_158 (47) = happyShift action_33
action_158 (17) = happyGoto action_166
action_158 (18) = happyGoto action_25
action_158 (19) = happyGoto action_26
action_158 _ = happyFail

action_159 (28) = happyShift action_27
action_159 (34) = happyShift action_28
action_159 (39) = happyShift action_29
action_159 (42) = happyShift action_30
action_159 (44) = happyShift action_31
action_159 (45) = happyShift action_32
action_159 (47) = happyShift action_33
action_159 (17) = happyGoto action_165
action_159 (18) = happyGoto action_25
action_159 (19) = happyGoto action_26
action_159 _ = happyFail

action_160 (28) = happyShift action_27
action_160 (34) = happyShift action_28
action_160 (39) = happyShift action_29
action_160 (42) = happyShift action_30
action_160 (44) = happyShift action_31
action_160 (45) = happyShift action_32
action_160 (47) = happyShift action_33
action_160 (17) = happyGoto action_164
action_160 (18) = happyGoto action_25
action_160 (19) = happyGoto action_26
action_160 _ = happyFail

action_161 (28) = happyShift action_27
action_161 (34) = happyShift action_28
action_161 (39) = happyShift action_29
action_161 (42) = happyShift action_30
action_161 (44) = happyShift action_31
action_161 (45) = happyShift action_32
action_161 (47) = happyShift action_33
action_161 (17) = happyGoto action_163
action_161 (18) = happyGoto action_25
action_161 (19) = happyGoto action_26
action_161 _ = happyFail

action_162 _ = happyReduce_8

action_163 _ = happyReduce_35

action_164 _ = happyReduce_32

action_165 _ = happyReduce_33

action_166 _ = happyReduce_34

action_167 (40) = happyShift action_188
action_167 _ = happyFail

action_168 (51) = happyShift action_187
action_168 _ = happyFail

action_169 _ = happyReduce_52

action_170 (28) = happyShift action_62
action_170 (34) = happyShift action_63
action_170 (39) = happyShift action_64
action_170 (42) = happyShift action_65
action_170 (44) = happyShift action_66
action_170 (45) = happyShift action_67
action_170 (47) = happyShift action_68
action_170 (20) = happyGoto action_186
action_170 (21) = happyGoto action_60
action_170 (22) = happyGoto action_61
action_170 _ = happyFail

action_171 (28) = happyShift action_62
action_171 (34) = happyShift action_63
action_171 (39) = happyShift action_64
action_171 (42) = happyShift action_65
action_171 (44) = happyShift action_66
action_171 (45) = happyShift action_67
action_171 (47) = happyShift action_68
action_171 (20) = happyGoto action_185
action_171 (21) = happyGoto action_60
action_171 (22) = happyGoto action_61
action_171 _ = happyFail

action_172 (41) = happyShift action_184
action_172 _ = happyFail

action_173 (35) = happyShift action_183
action_173 _ = happyFail

action_174 (28) = happyShift action_62
action_174 (34) = happyShift action_63
action_174 (39) = happyShift action_64
action_174 (42) = happyShift action_65
action_174 (44) = happyShift action_66
action_174 (45) = happyShift action_67
action_174 (47) = happyShift action_68
action_174 (20) = happyGoto action_182
action_174 (21) = happyGoto action_60
action_174 (22) = happyGoto action_61
action_174 _ = happyFail

action_175 (28) = happyShift action_62
action_175 (34) = happyShift action_63
action_175 (39) = happyShift action_64
action_175 (42) = happyShift action_65
action_175 (44) = happyShift action_66
action_175 (45) = happyShift action_67
action_175 (47) = happyShift action_68
action_175 (20) = happyGoto action_181
action_175 (21) = happyGoto action_60
action_175 (22) = happyGoto action_61
action_175 _ = happyFail

action_176 _ = happyReduce_10

action_177 _ = happyReduce_9

action_178 (33) = happyShift action_180
action_178 _ = happyFail

action_179 _ = happyReduce_54

action_180 (28) = happyShift action_27
action_180 (34) = happyShift action_28
action_180 (39) = happyShift action_29
action_180 (42) = happyShift action_30
action_180 (44) = happyShift action_31
action_180 (45) = happyShift action_32
action_180 (47) = happyShift action_33
action_180 (17) = happyGoto action_191
action_180 (18) = happyGoto action_25
action_180 (19) = happyGoto action_26
action_180 _ = happyFail

action_181 _ = happyReduce_46

action_182 _ = happyReduce_43

action_183 _ = happyReduce_59

action_184 (28) = happyShift action_62
action_184 (34) = happyShift action_148
action_184 (39) = happyShift action_64
action_184 (42) = happyShift action_65
action_184 (43) = happyShift action_149
action_184 (44) = happyShift action_66
action_184 (45) = happyShift action_67
action_184 (47) = happyShift action_68
action_184 (56) = happyShift action_150
action_184 (20) = happyGoto action_145
action_184 (21) = happyGoto action_60
action_184 (22) = happyGoto action_61
action_184 (24) = happyGoto action_146
action_184 (26) = happyGoto action_190
action_184 _ = happyFail

action_185 _ = happyReduce_44

action_186 _ = happyReduce_45

action_187 (28) = happyShift action_14
action_187 (34) = happyShift action_15
action_187 (36) = happyShift action_16
action_187 (45) = happyShift action_17
action_187 (46) = happyShift action_18
action_187 (48) = happyShift action_19
action_187 (49) = happyShift action_20
action_187 (52) = happyShift action_21
action_187 (53) = happyShift action_22
action_187 (54) = happyShift action_23
action_187 (10) = happyGoto action_189
action_187 (11) = happyGoto action_11
action_187 (12) = happyGoto action_12
action_187 (13) = happyGoto action_13
action_187 _ = happyFail

action_188 _ = happyReduce_12

action_189 _ = happyReduce_11

action_190 (33) = happyShift action_193
action_190 _ = happyFail

action_191 (37) = happyShift action_192
action_191 _ = happyFail

action_192 _ = happyReduce_23

action_193 (34) = happyShift action_195
action_193 (43) = happyShift action_149
action_193 (56) = happyShift action_150
action_193 (24) = happyGoto action_194
action_193 _ = happyFail

action_194 _ = happyReduce_57

action_195 (34) = happyShift action_195
action_195 (43) = happyShift action_149
action_195 (56) = happyShift action_150
action_195 (24) = happyGoto action_173
action_195 _ = happyFail

happyReduce_5 = happySpecReduce_0  8 happyReduction_5
happyReduction_5  =  HappyAbsSyn8
		 (CmdsStart
	)

happyReduce_6 = happySpecReduce_2  8 happyReduction_6
happyReduction_6 (HappyAbsSyn8  happy_var_2)
	(HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn8
		 (CmdsNext happy_var_1 happy_var_2
	)
happyReduction_6 _ _  = notHappyAtAll 

happyReduce_7 = happyReduce 4 9 happyReduction_7
happyReduction_7 (_ `HappyStk`
	(HappyAbsSyn10  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (TermCmd (tStr happy_var_1) happy_var_3
	) `HappyStk` happyRest

happyReduce_8 = happyReduce 5 9 happyReduction_8
happyReduction_8 (_ `HappyStk`
	(HappyAbsSyn17  happy_var_4) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (TypeCmd (tStr happy_var_1) happy_var_4
	) `HappyStk` happyRest

happyReduce_9 = happyReduce 6 10 happyReduction_9
happyReduction_9 ((HappyAbsSyn10  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn17  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (TmLambda (tStr happy_var_2) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_10 = happyReduce 6 10 happyReduction_10
happyReduction_10 ((HappyAbsSyn10  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn25  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (TmLambdaE (tStr happy_var_2) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_11 = happyReduce 8 10 happyReduction_11
happyReduction_11 ((HappyAbsSyn10  happy_var_8) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn10  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (Rho happy_var_2 (tStr happy_var_4) happy_var_6 happy_var_8
	) `HappyStk` happyRest

happyReduce_12 = happyReduce 7 10 happyReduction_12
happyReduction_12 (_ `HappyStk`
	(HappyAbsSyn14  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn10  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (Phi happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_13 = happyReduce 4 10 happyReduction_13
happyReduction_13 ((HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (Delta happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_14 = happySpecReduce_1  10 happyReduction_14
happyReduction_14 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (happy_var_1
	)
happyReduction_14 _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_2  11 happyReduction_15
happyReduction_15 (HappyAbsSyn10  happy_var_2)
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (TmAppTm happy_var_1 happy_var_2
	)
happyReduction_15 _ _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_3  11 happyReduction_16
happyReduction_16 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (TmAppTmE happy_var_1 happy_var_3
	)
happyReduction_16 _ _ _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_3  11 happyReduction_17
happyReduction_17 (HappyAbsSyn17  happy_var_3)
	_
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (TmAppTp happy_var_1 happy_var_3
	)
happyReduction_17 _ _ _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_1  11 happyReduction_18
happyReduction_18 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (happy_var_1
	)
happyReduction_18 _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_2  12 happyReduction_19
happyReduction_19 (HappyAbsSyn10  happy_var_2)
	_
	 =  HappyAbsSyn10
		 (Sigma happy_var_2
	)
happyReduction_19 _ _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_1  12 happyReduction_20
happyReduction_20 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (happy_var_1
	)
happyReduction_20 _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_1  13 happyReduction_21
happyReduction_21 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn10
		 (TmVar (tStr happy_var_1)
	)
happyReduction_21 _  = notHappyAtAll 

happyReduce_22 = happyReduce 5 13 happyReduction_22
happyReduction_22 (_ `HappyStk`
	(HappyAbsSyn14  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn14  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (Beta happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_23 = happyReduce 9 13 happyReduction_23
happyReduction_23 (_ `HappyStk`
	(HappyAbsSyn17  happy_var_8) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn10  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (IotaPair happy_var_2 happy_var_4 (tStr happy_var_6) happy_var_8
	) `HappyStk` happyRest

happyReduce_24 = happySpecReduce_2  13 happyReduction_24
happyReduction_24 (HappyTerminal happy_var_2)
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (mkIotaProj happy_var_1 (tStr happy_var_2)
	)
happyReduction_24 _ _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_3  13 happyReduction_25
happyReduction_25 _
	(HappyAbsSyn10  happy_var_2)
	_
	 =  HappyAbsSyn10
		 (happy_var_2
	)
happyReduction_25 _ _ _  = notHappyAtAll 

happyReduce_26 = happyReduce 4 14 happyReduction_26
happyReduction_26 ((HappyAbsSyn14  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn14
		 (PureLambda (tStr happy_var_2) happy_var_4
	) `HappyStk` happyRest

happyReduce_27 = happySpecReduce_1  14 happyReduction_27
happyReduction_27 (HappyAbsSyn14  happy_var_1)
	 =  HappyAbsSyn14
		 (happy_var_1
	)
happyReduction_27 _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_2  15 happyReduction_28
happyReduction_28 (HappyAbsSyn14  happy_var_2)
	(HappyAbsSyn14  happy_var_1)
	 =  HappyAbsSyn14
		 (PureApp happy_var_1 happy_var_2
	)
happyReduction_28 _ _  = notHappyAtAll 

happyReduce_29 = happySpecReduce_1  15 happyReduction_29
happyReduction_29 (HappyAbsSyn14  happy_var_1)
	 =  HappyAbsSyn14
		 (happy_var_1
	)
happyReduction_29 _  = notHappyAtAll 

happyReduce_30 = happySpecReduce_1  16 happyReduction_30
happyReduction_30 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn14
		 (PureVar (tStr happy_var_1)
	)
happyReduction_30 _  = notHappyAtAll 

happyReduce_31 = happySpecReduce_3  16 happyReduction_31
happyReduction_31 _
	(HappyAbsSyn14  happy_var_2)
	_
	 =  HappyAbsSyn14
		 (happy_var_2
	)
happyReduction_31 _ _ _  = notHappyAtAll 

happyReduce_32 = happyReduce 6 17 happyReduction_32
happyReduction_32 ((HappyAbsSyn17  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn25  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn17
		 (TpLambda (tStr happy_var_2) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_33 = happyReduce 6 17 happyReduction_33
happyReduction_33 ((HappyAbsSyn17  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn25  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn17
		 (TpAll (tStr happy_var_2) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_34 = happyReduce 6 17 happyReduction_34
happyReduction_34 ((HappyAbsSyn17  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn17  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn17
		 (TpPi (tStr happy_var_2) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_35 = happyReduce 6 17 happyReduction_35
happyReduction_35 ((HappyAbsSyn17  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn17  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn17
		 (Iota (tStr happy_var_2) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_36 = happySpecReduce_1  17 happyReduction_36
happyReduction_36 (HappyAbsSyn17  happy_var_1)
	 =  HappyAbsSyn17
		 (happy_var_1
	)
happyReduction_36 _  = notHappyAtAll 

happyReduce_37 = happySpecReduce_3  18 happyReduction_37
happyReduction_37 (HappyAbsSyn17  happy_var_3)
	_
	(HappyAbsSyn17  happy_var_1)
	 =  HappyAbsSyn17
		 (TpAppTp happy_var_1 happy_var_3
	)
happyReduction_37 _ _ _  = notHappyAtAll 

happyReduce_38 = happySpecReduce_2  18 happyReduction_38
happyReduction_38 (HappyAbsSyn10  happy_var_2)
	(HappyAbsSyn17  happy_var_1)
	 =  HappyAbsSyn17
		 (TpAppTm happy_var_1 happy_var_2
	)
happyReduction_38 _ _  = notHappyAtAll 

happyReduce_39 = happySpecReduce_1  18 happyReduction_39
happyReduction_39 (HappyAbsSyn17  happy_var_1)
	 =  HappyAbsSyn17
		 (happy_var_1
	)
happyReduction_39 _  = notHappyAtAll 

happyReduce_40 = happySpecReduce_1  19 happyReduction_40
happyReduction_40 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn17
		 (TpVar (tStr happy_var_1)
	)
happyReduction_40 _  = notHappyAtAll 

happyReduce_41 = happyReduce 5 19 happyReduction_41
happyReduction_41 (_ `HappyStk`
	(HappyAbsSyn14  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn14  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn17
		 (TpEq happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_42 = happySpecReduce_3  19 happyReduction_42
happyReduction_42 _
	(HappyAbsSyn17  happy_var_2)
	_
	 =  HappyAbsSyn17
		 (happy_var_2
	)
happyReduction_42 _ _ _  = notHappyAtAll 

happyReduce_43 = happyReduce 6 20 happyReduction_43
happyReduction_43 ((HappyAbsSyn20  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn26  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn20
		 (TpLambda (tStr happy_var_2) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_44 = happyReduce 6 20 happyReduction_44
happyReduction_44 ((HappyAbsSyn20  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn26  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn20
		 (TpAll (tStr happy_var_2) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_45 = happyReduce 6 20 happyReduction_45
happyReduction_45 ((HappyAbsSyn20  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn20
		 (TpPi (tStr happy_var_2) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_46 = happyReduce 6 20 happyReduction_46
happyReduction_46 ((HappyAbsSyn20  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn20
		 (Iota (tStr happy_var_2) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_47 = happySpecReduce_1  20 happyReduction_47
happyReduction_47 (HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn20
		 (happy_var_1
	)
happyReduction_47 _  = notHappyAtAll 

happyReduce_48 = happySpecReduce_3  21 happyReduction_48
happyReduction_48 (HappyAbsSyn20  happy_var_3)
	_
	(HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn20
		 (TpAppTp happy_var_1 happy_var_3
	)
happyReduction_48 _ _ _  = notHappyAtAll 

happyReduce_49 = happySpecReduce_2  21 happyReduction_49
happyReduction_49 (HappyAbsSyn14  happy_var_2)
	(HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn20
		 (TpAppTm happy_var_1 happy_var_2
	)
happyReduction_49 _ _  = notHappyAtAll 

happyReduce_50 = happySpecReduce_1  21 happyReduction_50
happyReduction_50 (HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn20
		 (happy_var_1
	)
happyReduction_50 _  = notHappyAtAll 

happyReduce_51 = happySpecReduce_1  22 happyReduction_51
happyReduction_51 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn20
		 (TpVar (tStr happy_var_1)
	)
happyReduction_51 _  = notHappyAtAll 

happyReduce_52 = happyReduce 5 22 happyReduction_52
happyReduction_52 (_ `HappyStk`
	(HappyAbsSyn14  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn14  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn20
		 (TpEq happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_53 = happySpecReduce_3  22 happyReduction_53
happyReduction_53 _
	(HappyAbsSyn20  happy_var_2)
	_
	 =  HappyAbsSyn20
		 (happy_var_2
	)
happyReduction_53 _ _ _  = notHappyAtAll 

happyReduce_54 = happyReduce 6 23 happyReduction_54
happyReduction_54 ((HappyAbsSyn23  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn25  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 (KdPi (tStr happy_var_2) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_55 = happySpecReduce_1  23 happyReduction_55
happyReduction_55 _
	 =  HappyAbsSyn23
		 (Star
	)

happyReduce_56 = happySpecReduce_3  23 happyReduction_56
happyReduction_56 _
	(HappyAbsSyn23  happy_var_2)
	_
	 =  HappyAbsSyn23
		 (happy_var_2
	)
happyReduction_56 _ _ _  = notHappyAtAll 

happyReduce_57 = happyReduce 6 24 happyReduction_57
happyReduction_57 ((HappyAbsSyn24  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn26  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn24
		 (KdPi (tStr happy_var_2) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_58 = happySpecReduce_1  24 happyReduction_58
happyReduction_58 _
	 =  HappyAbsSyn24
		 (Star
	)

happyReduce_59 = happySpecReduce_3  24 happyReduction_59
happyReduction_59 _
	(HappyAbsSyn24  happy_var_2)
	_
	 =  HappyAbsSyn24
		 (happy_var_2
	)
happyReduction_59 _ _ _  = notHappyAtAll 

happyReduce_60 = happySpecReduce_1  25 happyReduction_60
happyReduction_60 (HappyAbsSyn17  happy_var_1)
	 =  HappyAbsSyn25
		 (Tkt happy_var_1
	)
happyReduction_60 _  = notHappyAtAll 

happyReduce_61 = happySpecReduce_1  25 happyReduction_61
happyReduction_61 (HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn25
		 (Tkk happy_var_1
	)
happyReduction_61 _  = notHappyAtAll 

happyReduce_62 = happySpecReduce_1  26 happyReduction_62
happyReduction_62 (HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn26
		 (Tkt happy_var_1
	)
happyReduction_62 _  = notHappyAtAll 

happyReduce_63 = happySpecReduce_1  26 happyReduction_63
happyReduction_63 (HappyAbsSyn24  happy_var_1)
	 =  HappyAbsSyn26
		 (Tkk happy_var_1
	)
happyReduction_63 _  = notHappyAtAll 

happyReduce_64 = happySpecReduce_1  27 happyReduction_64
happyReduction_64 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn27
		 (happy_var_1
	)
happyReduction_64 _  = notHappyAtAll 

happyReduce_65 = happySpecReduce_1  27 happyReduction_65
happyReduction_65 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn27
		 (happy_var_1
	)
happyReduction_65 _  = notHappyAtAll 

happyNewToken action sts stk
	= lexer(\tk -> 
	let cont i = action i i tk (HappyState action) sts stk in
	case tk of {
	Token _ TEOF -> action 58 58 tk (HappyState action) sts stk;
	Token _  (TVar _) -> cont 28;
	Token _  (TProj _) -> cont 29;
	Token _  (TSym "_") -> cont 30;
	Token happy_dollar_dollar (TSym "=") -> cont 31;
	Token happy_dollar_dollar (TSym "◂") -> cont 32;
	Token happy_dollar_dollar (TSym ".") -> cont 33;
	Token happy_dollar_dollar (TSym "(") -> cont 34;
	Token happy_dollar_dollar (TSym ")") -> cont 35;
	Token happy_dollar_dollar (TSym "[") -> cont 36;
	Token happy_dollar_dollar (TSym "]") -> cont 37;
	Token happy_dollar_dollar (TSym ",") -> cont 38;
	Token happy_dollar_dollar (TSym "{") -> cont 39;
	Token happy_dollar_dollar (TSym "}") -> cont 40;
	Token happy_dollar_dollar (TSym ":") -> cont 41;
	Token happy_dollar_dollar (TSym "Π") -> cont 42;
	Token happy_dollar_dollar (TSym "π") -> cont 43;
	Token happy_dollar_dollar (TSym "∀") -> cont 44;
	Token happy_dollar_dollar (TSym "λ") -> cont 45;
	Token happy_dollar_dollar (TSym "Λ") -> cont 46;
	Token happy_dollar_dollar (TSym "ι") -> cont 47;
	Token happy_dollar_dollar (TSym "β") -> cont 48;
	Token happy_dollar_dollar (TSym "δ") -> cont 49;
	Token happy_dollar_dollar (TSym "·") -> cont 50;
	Token happy_dollar_dollar (TSym "-") -> cont 51;
	Token happy_dollar_dollar (TSym "ς") -> cont 52;
	Token happy_dollar_dollar (TSym "ρ") -> cont 53;
	Token happy_dollar_dollar (TSym "φ") -> cont 54;
	Token happy_dollar_dollar (TSym "≃") -> cont 55;
	Token happy_dollar_dollar (TSym "★") -> cont 56;
	Token happy_dollar_dollar (TSym "@") -> cont 57;
	_ -> happyError' tk
	})

happyError_ 58 tk = happyError' tk
happyError_ _ tk = happyError' tk

happyThen :: () => Alex a -> (a -> Alex b) -> Alex b
happyThen = (>>=)
happyReturn :: () => a -> Alex a
happyReturn = (return)
happyThen1 = happyThen
happyReturn1 :: () => a -> Alex a
happyReturn1 = happyReturn
happyError' :: () => (Token) -> Alex a
happyError' tk = parseError tk

cedilleCoreParser = happySomeParser where
  happySomeParser = happyThen (happyParse action_0) (\x -> case x of {HappyAbsSyn8 z -> happyReturn z; _other -> notHappyAtAll })

cmd = happySomeParser where
  happySomeParser = happyThen (happyParse action_1) (\x -> case x of {HappyAbsSyn9 z -> happyReturn z; _other -> notHappyAtAll })

types = happySomeParser where
  happySomeParser = happyThen (happyParse action_2) (\x -> case x of {HappyAbsSyn17 z -> happyReturn z; _other -> notHappyAtAll })

term = happySomeParser where
  happySomeParser = happyThen (happyParse action_3) (\x -> case x of {HappyAbsSyn10 z -> happyReturn z; _other -> notHappyAtAll })

kind = happySomeParser where
  happySomeParser = happyThen (happyParse action_4) (\x -> case x of {HappyAbsSyn23 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


lexer :: (Token -> Alex a) -> Alex a
lexer f = alexMonadScanErrOffset >>= f  

mkIotaProj :: Term -> String -> Term
mkIotaProj tm "1" = IotaProj1 tm
mkIotaProj tm "2" = IotaProj2 tm
mkIotaProj tm _ = TmVar "This should never happen (IotaProj with a number other than 1 or 2"

parseError :: Token -> Alex a
parseError (Token (AlexPn p _ _) t) = alexError $ "P" ++ show (p + 1)

parseStr :: String -> Either (Either String String) Cmds
parseStr s = case runAlex s $ cedilleCoreParser of
               Prelude.Left  s' -> case head s' of {
                                     'L' -> Prelude.Left (Prelude.Left  (tail s'));
                                     'P' -> Prelude.Left (Prelude.Right (tail s'));
                                     _   -> Prelude.Left (Prelude.Right "0") -- This should never happen
                                   }
               Prelude.Right r  -> Prelude.Right r

main :: IO ()
main = do  
  [ file ] <- getArgs
  cnt      <- readFile file
  case parseStr cnt of 
    Prelude.Left  (Prelude.Left  errMsg) -> writeFile (file ++ "-result") errMsg
    Prelude.Left  (Prelude.Right errMsg) -> writeFile (file ++ "-result") errMsg
    Prelude.Right res                    -> writeFile (file ++ "-result") (show res)
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 8 "<command-line>" #-}
# 1 "/usr/include/stdc-predef.h" 1 3 4

# 17 "/usr/include/stdc-predef.h" 3 4










































{-# LINE 8 "<command-line>" #-}
{-# LINE 1 "/usr/lib/ghc/include/ghcversion.h" #-}

















{-# LINE 8 "<command-line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 13 "templates/GenericTemplate.hs" #-}

{-# LINE 46 "templates/GenericTemplate.hs" #-}








{-# LINE 67 "templates/GenericTemplate.hs" #-}

{-# LINE 77 "templates/GenericTemplate.hs" #-}

{-# LINE 86 "templates/GenericTemplate.hs" #-}

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is (1), it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action

{-# LINE 155 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Int ->                    -- token number
         Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k - ((1) :: Int)) sts of
         sts1@(((st1@(HappyState (action))):(_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
         let drop_stk = happyDropStk k stk





             new_state = action

          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n - ((1) :: Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n - ((1)::Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction

{-# LINE 256 "templates/GenericTemplate.hs" #-}
happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery ((1) is the error token)

-- parse error if we are in recovery and we fail again
happyFail (1) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  (1) tk old_st (((HappyState (action))):(sts)) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        action (1) (1) tk (HappyState (action)) sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
        action (1) (1) tk (HappyState (action)) sts ( (HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.

{-# LINE 322 "templates/GenericTemplate.hs" #-}
{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
