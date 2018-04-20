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
 action_195,
 action_196,
 action_197,
 action_198,
 action_199,
 action_200,
 action_201 :: () => Int -> ({-HappyReduction (Alex) = -}
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
 happyReduce_63 :: () => ({-HappyReduction (Alex) = -}
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> (Alex) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> (Alex) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> (Alex) HappyAbsSyn)

action_0 (27) = happyShift action_35
action_0 (8) = happyGoto action_36
action_0 (9) = happyGoto action_37
action_0 _ = happyReduce_5

action_1 (27) = happyShift action_35
action_1 (9) = happyGoto action_34
action_1 _ = happyFail

action_2 (27) = happyShift action_27
action_2 (32) = happyShift action_28
action_2 (37) = happyShift action_29
action_2 (40) = happyShift action_30
action_2 (41) = happyShift action_31
action_2 (42) = happyShift action_32
action_2 (44) = happyShift action_33
action_2 (17) = happyGoto action_24
action_2 (18) = happyGoto action_25
action_2 (19) = happyGoto action_26
action_2 _ = happyFail

action_3 (27) = happyShift action_14
action_3 (32) = happyShift action_15
action_3 (34) = happyShift action_16
action_3 (42) = happyShift action_17
action_3 (43) = happyShift action_18
action_3 (45) = happyShift action_19
action_3 (46) = happyShift action_20
action_3 (49) = happyShift action_21
action_3 (50) = happyShift action_22
action_3 (51) = happyShift action_23
action_3 (10) = happyGoto action_10
action_3 (11) = happyGoto action_11
action_3 (12) = happyGoto action_12
action_3 (13) = happyGoto action_13
action_3 _ = happyFail

action_4 (32) = happyShift action_7
action_4 (40) = happyShift action_8
action_4 (53) = happyShift action_9
action_4 (23) = happyGoto action_6
action_4 _ = happyFail

action_5 _ = happyFail

action_6 (55) = happyAccept
action_6 _ = happyFail

action_7 (32) = happyShift action_7
action_7 (40) = happyShift action_8
action_7 (53) = happyShift action_9
action_7 (23) = happyGoto action_77
action_7 _ = happyFail

action_8 (27) = happyShift action_76
action_8 _ = happyFail

action_9 _ = happyReduce_55

action_10 (55) = happyAccept
action_10 _ = happyFail

action_11 (27) = happyShift action_14
action_11 (32) = happyShift action_15
action_11 (34) = happyShift action_16
action_11 (45) = happyShift action_19
action_11 (47) = happyShift action_74
action_11 (48) = happyShift action_75
action_11 (13) = happyGoto action_73
action_11 _ = happyReduce_14

action_12 _ = happyReduce_18

action_13 (28) = happyShift action_72
action_13 _ = happyReduce_20

action_14 _ = happyReduce_21

action_15 (27) = happyShift action_14
action_15 (32) = happyShift action_15
action_15 (34) = happyShift action_16
action_15 (42) = happyShift action_17
action_15 (43) = happyShift action_18
action_15 (45) = happyShift action_19
action_15 (46) = happyShift action_20
action_15 (49) = happyShift action_21
action_15 (50) = happyShift action_22
action_15 (51) = happyShift action_23
action_15 (10) = happyGoto action_71
action_15 (11) = happyGoto action_11
action_15 (12) = happyGoto action_12
action_15 (13) = happyGoto action_13
action_15 _ = happyFail

action_16 (27) = happyShift action_14
action_16 (32) = happyShift action_15
action_16 (34) = happyShift action_16
action_16 (42) = happyShift action_17
action_16 (43) = happyShift action_18
action_16 (45) = happyShift action_19
action_16 (46) = happyShift action_20
action_16 (49) = happyShift action_21
action_16 (50) = happyShift action_22
action_16 (51) = happyShift action_23
action_16 (10) = happyGoto action_70
action_16 (11) = happyGoto action_11
action_16 (12) = happyGoto action_12
action_16 (13) = happyGoto action_13
action_16 _ = happyFail

action_17 (27) = happyShift action_69
action_17 _ = happyFail

action_18 (27) = happyShift action_68
action_18 _ = happyFail

action_19 (27) = happyShift action_48
action_19 (32) = happyShift action_49
action_19 (16) = happyGoto action_67
action_19 _ = happyFail

action_20 (27) = happyShift action_60
action_20 (32) = happyShift action_61
action_20 (37) = happyShift action_62
action_20 (40) = happyShift action_63
action_20 (41) = happyShift action_64
action_20 (42) = happyShift action_65
action_20 (44) = happyShift action_66
action_20 (20) = happyGoto action_57
action_20 (21) = happyGoto action_58
action_20 (22) = happyGoto action_59
action_20 _ = happyFail

action_21 (27) = happyShift action_14
action_21 (32) = happyShift action_15
action_21 (34) = happyShift action_16
action_21 (45) = happyShift action_19
action_21 (49) = happyShift action_21
action_21 (12) = happyGoto action_56
action_21 (13) = happyGoto action_13
action_21 _ = happyFail

action_22 (27) = happyShift action_14
action_22 (32) = happyShift action_15
action_22 (34) = happyShift action_16
action_22 (45) = happyShift action_19
action_22 (49) = happyShift action_21
action_22 (12) = happyGoto action_55
action_22 (13) = happyGoto action_13
action_22 _ = happyFail

action_23 (27) = happyShift action_14
action_23 (32) = happyShift action_15
action_23 (34) = happyShift action_16
action_23 (45) = happyShift action_19
action_23 (49) = happyShift action_21
action_23 (12) = happyGoto action_54
action_23 (13) = happyGoto action_13
action_23 _ = happyFail

action_24 (55) = happyAccept
action_24 _ = happyFail

action_25 (27) = happyShift action_14
action_25 (32) = happyShift action_15
action_25 (34) = happyShift action_16
action_25 (45) = happyShift action_19
action_25 (47) = happyShift action_53
action_25 (13) = happyGoto action_52
action_25 _ = happyReduce_36

action_26 _ = happyReduce_39

action_27 _ = happyReduce_40

action_28 (27) = happyShift action_27
action_28 (32) = happyShift action_28
action_28 (37) = happyShift action_29
action_28 (40) = happyShift action_30
action_28 (41) = happyShift action_31
action_28 (42) = happyShift action_32
action_28 (44) = happyShift action_33
action_28 (17) = happyGoto action_51
action_28 (18) = happyGoto action_25
action_28 (19) = happyGoto action_26
action_28 _ = happyFail

action_29 (27) = happyShift action_48
action_29 (32) = happyShift action_49
action_29 (42) = happyShift action_50
action_29 (14) = happyGoto action_45
action_29 (15) = happyGoto action_46
action_29 (16) = happyGoto action_47
action_29 _ = happyFail

action_30 (27) = happyShift action_44
action_30 _ = happyFail

action_31 (27) = happyShift action_43
action_31 _ = happyFail

action_32 (27) = happyShift action_42
action_32 _ = happyFail

action_33 (27) = happyShift action_41
action_33 _ = happyFail

action_34 (55) = happyAccept
action_34 _ = happyFail

action_35 (29) = happyShift action_39
action_35 (30) = happyShift action_40
action_35 _ = happyFail

action_36 (55) = happyAccept
action_36 _ = happyFail

action_37 (27) = happyShift action_35
action_37 (8) = happyGoto action_38
action_37 (9) = happyGoto action_37
action_37 _ = happyReduce_5

action_38 _ = happyReduce_6

action_39 (27) = happyShift action_14
action_39 (32) = happyShift action_15
action_39 (34) = happyShift action_16
action_39 (42) = happyShift action_17
action_39 (43) = happyShift action_18
action_39 (45) = happyShift action_19
action_39 (46) = happyShift action_20
action_39 (49) = happyShift action_21
action_39 (50) = happyShift action_22
action_39 (51) = happyShift action_23
action_39 (10) = happyGoto action_109
action_39 (11) = happyGoto action_11
action_39 (12) = happyGoto action_12
action_39 (13) = happyGoto action_13
action_39 _ = happyFail

action_40 (29) = happyShift action_108
action_40 _ = happyFail

action_41 (39) = happyShift action_107
action_41 _ = happyFail

action_42 (39) = happyShift action_106
action_42 _ = happyFail

action_43 (39) = happyShift action_105
action_43 _ = happyFail

action_44 (39) = happyShift action_104
action_44 _ = happyFail

action_45 (52) = happyShift action_103
action_45 _ = happyFail

action_46 (27) = happyShift action_48
action_46 (32) = happyShift action_49
action_46 (16) = happyGoto action_102
action_46 _ = happyReduce_27

action_47 _ = happyReduce_29

action_48 _ = happyReduce_30

action_49 (27) = happyShift action_48
action_49 (32) = happyShift action_49
action_49 (42) = happyShift action_50
action_49 (14) = happyGoto action_101
action_49 (15) = happyGoto action_46
action_49 (16) = happyGoto action_47
action_49 _ = happyFail

action_50 (27) = happyShift action_100
action_50 _ = happyFail

action_51 (33) = happyShift action_99
action_51 _ = happyFail

action_52 (28) = happyShift action_72
action_52 _ = happyReduce_38

action_53 (27) = happyShift action_27
action_53 (32) = happyShift action_28
action_53 (37) = happyShift action_29
action_53 (19) = happyGoto action_98
action_53 _ = happyFail

action_54 (48) = happyShift action_97
action_54 _ = happyFail

action_55 (54) = happyShift action_96
action_55 _ = happyFail

action_56 _ = happyReduce_19

action_57 (48) = happyShift action_95
action_57 _ = happyFail

action_58 (27) = happyShift action_48
action_58 (32) = happyShift action_49
action_58 (47) = happyShift action_94
action_58 (16) = happyGoto action_93
action_58 _ = happyReduce_47

action_59 _ = happyReduce_50

action_60 _ = happyReduce_51

action_61 (27) = happyShift action_60
action_61 (32) = happyShift action_61
action_61 (37) = happyShift action_62
action_61 (40) = happyShift action_63
action_61 (41) = happyShift action_64
action_61 (42) = happyShift action_65
action_61 (44) = happyShift action_66
action_61 (20) = happyGoto action_92
action_61 (21) = happyGoto action_58
action_61 (22) = happyGoto action_59
action_61 _ = happyFail

action_62 (27) = happyShift action_48
action_62 (32) = happyShift action_49
action_62 (42) = happyShift action_50
action_62 (14) = happyGoto action_91
action_62 (15) = happyGoto action_46
action_62 (16) = happyGoto action_47
action_62 _ = happyFail

action_63 (27) = happyShift action_90
action_63 _ = happyFail

action_64 (27) = happyShift action_89
action_64 _ = happyFail

action_65 (27) = happyShift action_88
action_65 _ = happyFail

action_66 (27) = happyShift action_87
action_66 _ = happyFail

action_67 (37) = happyShift action_86
action_67 _ = happyFail

action_68 (39) = happyShift action_85
action_68 _ = happyFail

action_69 (39) = happyShift action_84
action_69 _ = happyFail

action_70 (36) = happyShift action_83
action_70 _ = happyFail

action_71 (33) = happyShift action_82
action_71 _ = happyFail

action_72 _ = happyReduce_24

action_73 (28) = happyShift action_72
action_73 _ = happyReduce_15

action_74 (27) = happyShift action_27
action_74 (32) = happyShift action_28
action_74 (37) = happyShift action_29
action_74 (19) = happyGoto action_81
action_74 _ = happyFail

action_75 (27) = happyShift action_14
action_75 (32) = happyShift action_15
action_75 (34) = happyShift action_16
action_75 (45) = happyShift action_19
action_75 (13) = happyGoto action_80
action_75 _ = happyFail

action_76 (39) = happyShift action_79
action_76 _ = happyFail

action_77 (33) = happyShift action_78
action_77 _ = happyFail

action_78 _ = happyReduce_56

action_79 (27) = happyShift action_27
action_79 (32) = happyShift action_116
action_79 (37) = happyShift action_29
action_79 (40) = happyShift action_117
action_79 (41) = happyShift action_31
action_79 (42) = happyShift action_32
action_79 (44) = happyShift action_33
action_79 (53) = happyShift action_9
action_79 (17) = happyGoto action_113
action_79 (18) = happyGoto action_25
action_79 (19) = happyGoto action_26
action_79 (23) = happyGoto action_114
action_79 (25) = happyGoto action_137
action_79 _ = happyFail

action_80 (28) = happyShift action_72
action_80 _ = happyReduce_16

action_81 _ = happyReduce_17

action_82 _ = happyReduce_25

action_83 (27) = happyShift action_14
action_83 (32) = happyShift action_15
action_83 (34) = happyShift action_16
action_83 (42) = happyShift action_17
action_83 (43) = happyShift action_18
action_83 (45) = happyShift action_19
action_83 (46) = happyShift action_20
action_83 (49) = happyShift action_21
action_83 (50) = happyShift action_22
action_83 (51) = happyShift action_23
action_83 (10) = happyGoto action_136
action_83 (11) = happyGoto action_11
action_83 (12) = happyGoto action_12
action_83 (13) = happyGoto action_13
action_83 _ = happyFail

action_84 (27) = happyShift action_27
action_84 (32) = happyShift action_28
action_84 (37) = happyShift action_29
action_84 (40) = happyShift action_30
action_84 (41) = happyShift action_31
action_84 (42) = happyShift action_32
action_84 (44) = happyShift action_33
action_84 (17) = happyGoto action_135
action_84 (18) = happyGoto action_25
action_84 (19) = happyGoto action_26
action_84 _ = happyFail

action_85 (27) = happyShift action_27
action_85 (32) = happyShift action_116
action_85 (37) = happyShift action_29
action_85 (40) = happyShift action_117
action_85 (41) = happyShift action_31
action_85 (42) = happyShift action_32
action_85 (44) = happyShift action_33
action_85 (53) = happyShift action_9
action_85 (17) = happyGoto action_113
action_85 (18) = happyGoto action_25
action_85 (19) = happyGoto action_26
action_85 (23) = happyGoto action_114
action_85 (25) = happyGoto action_134
action_85 _ = happyFail

action_86 (27) = happyShift action_48
action_86 (32) = happyShift action_49
action_86 (42) = happyShift action_50
action_86 (14) = happyGoto action_133
action_86 (15) = happyGoto action_46
action_86 (16) = happyGoto action_47
action_86 _ = happyFail

action_87 (39) = happyShift action_132
action_87 _ = happyFail

action_88 (39) = happyShift action_131
action_88 _ = happyFail

action_89 (39) = happyShift action_130
action_89 _ = happyFail

action_90 (39) = happyShift action_129
action_90 _ = happyFail

action_91 (52) = happyShift action_128
action_91 _ = happyFail

action_92 (33) = happyShift action_127
action_92 _ = happyFail

action_93 _ = happyReduce_49

action_94 (27) = happyShift action_60
action_94 (32) = happyShift action_61
action_94 (37) = happyShift action_62
action_94 (22) = happyGoto action_126
action_94 _ = happyFail

action_95 (27) = happyShift action_14
action_95 (32) = happyShift action_15
action_95 (34) = happyShift action_16
action_95 (42) = happyShift action_17
action_95 (43) = happyShift action_18
action_95 (45) = happyShift action_19
action_95 (46) = happyShift action_20
action_95 (49) = happyShift action_21
action_95 (50) = happyShift action_22
action_95 (51) = happyShift action_23
action_95 (10) = happyGoto action_125
action_95 (11) = happyGoto action_11
action_95 (12) = happyGoto action_12
action_95 (13) = happyGoto action_13
action_95 _ = happyFail

action_96 (27) = happyShift action_124
action_96 _ = happyFail

action_97 (27) = happyShift action_14
action_97 (32) = happyShift action_15
action_97 (34) = happyShift action_16
action_97 (42) = happyShift action_17
action_97 (43) = happyShift action_18
action_97 (45) = happyShift action_19
action_97 (46) = happyShift action_20
action_97 (49) = happyShift action_21
action_97 (50) = happyShift action_22
action_97 (51) = happyShift action_23
action_97 (10) = happyGoto action_123
action_97 (11) = happyGoto action_11
action_97 (12) = happyGoto action_12
action_97 (13) = happyGoto action_13
action_97 _ = happyFail

action_98 _ = happyReduce_37

action_99 _ = happyReduce_42

action_100 (31) = happyShift action_122
action_100 _ = happyFail

action_101 (33) = happyShift action_121
action_101 _ = happyFail

action_102 _ = happyReduce_28

action_103 (27) = happyShift action_48
action_103 (32) = happyShift action_49
action_103 (42) = happyShift action_50
action_103 (14) = happyGoto action_120
action_103 (15) = happyGoto action_46
action_103 (16) = happyGoto action_47
action_103 _ = happyFail

action_104 (27) = happyShift action_27
action_104 (32) = happyShift action_28
action_104 (37) = happyShift action_29
action_104 (40) = happyShift action_30
action_104 (41) = happyShift action_31
action_104 (42) = happyShift action_32
action_104 (44) = happyShift action_33
action_104 (17) = happyGoto action_119
action_104 (18) = happyGoto action_25
action_104 (19) = happyGoto action_26
action_104 _ = happyFail

action_105 (27) = happyShift action_27
action_105 (32) = happyShift action_116
action_105 (37) = happyShift action_29
action_105 (40) = happyShift action_117
action_105 (41) = happyShift action_31
action_105 (42) = happyShift action_32
action_105 (44) = happyShift action_33
action_105 (53) = happyShift action_9
action_105 (17) = happyGoto action_113
action_105 (18) = happyGoto action_25
action_105 (19) = happyGoto action_26
action_105 (23) = happyGoto action_114
action_105 (25) = happyGoto action_118
action_105 _ = happyFail

action_106 (27) = happyShift action_27
action_106 (32) = happyShift action_116
action_106 (37) = happyShift action_29
action_106 (40) = happyShift action_117
action_106 (41) = happyShift action_31
action_106 (42) = happyShift action_32
action_106 (44) = happyShift action_33
action_106 (53) = happyShift action_9
action_106 (17) = happyGoto action_113
action_106 (18) = happyGoto action_25
action_106 (19) = happyGoto action_26
action_106 (23) = happyGoto action_114
action_106 (25) = happyGoto action_115
action_106 _ = happyFail

action_107 (27) = happyShift action_27
action_107 (32) = happyShift action_28
action_107 (37) = happyShift action_29
action_107 (40) = happyShift action_30
action_107 (41) = happyShift action_31
action_107 (42) = happyShift action_32
action_107 (44) = happyShift action_33
action_107 (17) = happyGoto action_112
action_107 (18) = happyGoto action_25
action_107 (19) = happyGoto action_26
action_107 _ = happyFail

action_108 (27) = happyShift action_27
action_108 (32) = happyShift action_28
action_108 (37) = happyShift action_29
action_108 (40) = happyShift action_30
action_108 (41) = happyShift action_31
action_108 (42) = happyShift action_32
action_108 (44) = happyShift action_33
action_108 (17) = happyGoto action_111
action_108 (18) = happyGoto action_25
action_108 (19) = happyGoto action_26
action_108 _ = happyFail

action_109 (31) = happyShift action_110
action_109 _ = happyFail

action_110 _ = happyReduce_7

action_111 (31) = happyShift action_162
action_111 _ = happyFail

action_112 (31) = happyShift action_161
action_112 _ = happyFail

action_113 _ = happyReduce_60

action_114 _ = happyReduce_61

action_115 (31) = happyShift action_160
action_115 _ = happyFail

action_116 (27) = happyShift action_27
action_116 (32) = happyShift action_116
action_116 (37) = happyShift action_29
action_116 (40) = happyShift action_117
action_116 (41) = happyShift action_31
action_116 (42) = happyShift action_32
action_116 (44) = happyShift action_33
action_116 (53) = happyShift action_9
action_116 (17) = happyGoto action_51
action_116 (18) = happyGoto action_25
action_116 (19) = happyGoto action_26
action_116 (23) = happyGoto action_77
action_116 _ = happyFail

action_117 (27) = happyShift action_159
action_117 _ = happyFail

action_118 (31) = happyShift action_158
action_118 _ = happyFail

action_119 (31) = happyShift action_157
action_119 _ = happyFail

action_120 (38) = happyShift action_156
action_120 _ = happyFail

action_121 _ = happyReduce_31

action_122 (27) = happyShift action_48
action_122 (32) = happyShift action_49
action_122 (42) = happyShift action_50
action_122 (14) = happyGoto action_155
action_122 (15) = happyGoto action_46
action_122 (16) = happyGoto action_47
action_122 _ = happyFail

action_123 (37) = happyShift action_154
action_123 _ = happyFail

action_124 (31) = happyShift action_153
action_124 _ = happyFail

action_125 _ = happyReduce_13

action_126 _ = happyReduce_48

action_127 _ = happyReduce_53

action_128 (27) = happyShift action_48
action_128 (32) = happyShift action_49
action_128 (42) = happyShift action_50
action_128 (14) = happyGoto action_152
action_128 (15) = happyGoto action_46
action_128 (16) = happyGoto action_47
action_128 _ = happyFail

action_129 (27) = happyShift action_60
action_129 (32) = happyShift action_61
action_129 (37) = happyShift action_62
action_129 (40) = happyShift action_63
action_129 (41) = happyShift action_64
action_129 (42) = happyShift action_65
action_129 (44) = happyShift action_66
action_129 (20) = happyGoto action_151
action_129 (21) = happyGoto action_58
action_129 (22) = happyGoto action_59
action_129 _ = happyFail

action_130 (27) = happyShift action_60
action_130 (32) = happyShift action_147
action_130 (37) = happyShift action_62
action_130 (40) = happyShift action_148
action_130 (41) = happyShift action_64
action_130 (42) = happyShift action_65
action_130 (44) = happyShift action_66
action_130 (53) = happyShift action_149
action_130 (20) = happyGoto action_144
action_130 (21) = happyGoto action_58
action_130 (22) = happyGoto action_59
action_130 (24) = happyGoto action_145
action_130 (26) = happyGoto action_150
action_130 _ = happyFail

action_131 (27) = happyShift action_60
action_131 (32) = happyShift action_147
action_131 (37) = happyShift action_62
action_131 (40) = happyShift action_148
action_131 (41) = happyShift action_64
action_131 (42) = happyShift action_65
action_131 (44) = happyShift action_66
action_131 (53) = happyShift action_149
action_131 (20) = happyGoto action_144
action_131 (21) = happyGoto action_58
action_131 (22) = happyGoto action_59
action_131 (24) = happyGoto action_145
action_131 (26) = happyGoto action_146
action_131 _ = happyFail

action_132 (27) = happyShift action_60
action_132 (32) = happyShift action_61
action_132 (37) = happyShift action_62
action_132 (40) = happyShift action_63
action_132 (41) = happyShift action_64
action_132 (42) = happyShift action_65
action_132 (44) = happyShift action_66
action_132 (20) = happyGoto action_143
action_132 (21) = happyGoto action_58
action_132 (22) = happyGoto action_59
action_132 _ = happyFail

action_133 (38) = happyShift action_142
action_133 _ = happyFail

action_134 (31) = happyShift action_141
action_134 _ = happyFail

action_135 (31) = happyShift action_140
action_135 _ = happyFail

action_136 (54) = happyShift action_139
action_136 _ = happyFail

action_137 (31) = happyShift action_138
action_137 _ = happyFail

action_138 (32) = happyShift action_7
action_138 (40) = happyShift action_8
action_138 (53) = happyShift action_9
action_138 (23) = happyGoto action_180
action_138 _ = happyFail

action_139 (27) = happyShift action_179
action_139 _ = happyFail

action_140 (27) = happyShift action_14
action_140 (32) = happyShift action_15
action_140 (34) = happyShift action_16
action_140 (42) = happyShift action_17
action_140 (43) = happyShift action_18
action_140 (45) = happyShift action_19
action_140 (46) = happyShift action_20
action_140 (49) = happyShift action_21
action_140 (50) = happyShift action_22
action_140 (51) = happyShift action_23
action_140 (10) = happyGoto action_178
action_140 (11) = happyGoto action_11
action_140 (12) = happyGoto action_12
action_140 (13) = happyGoto action_13
action_140 _ = happyFail

action_141 (27) = happyShift action_14
action_141 (32) = happyShift action_15
action_141 (34) = happyShift action_16
action_141 (42) = happyShift action_17
action_141 (43) = happyShift action_18
action_141 (45) = happyShift action_19
action_141 (46) = happyShift action_20
action_141 (49) = happyShift action_21
action_141 (50) = happyShift action_22
action_141 (51) = happyShift action_23
action_141 (10) = happyGoto action_177
action_141 (11) = happyGoto action_11
action_141 (12) = happyGoto action_12
action_141 (13) = happyGoto action_13
action_141 _ = happyFail

action_142 _ = happyReduce_22

action_143 (31) = happyShift action_176
action_143 _ = happyFail

action_144 _ = happyReduce_62

action_145 _ = happyReduce_63

action_146 (31) = happyShift action_175
action_146 _ = happyFail

action_147 (27) = happyShift action_60
action_147 (32) = happyShift action_147
action_147 (37) = happyShift action_62
action_147 (40) = happyShift action_148
action_147 (41) = happyShift action_64
action_147 (42) = happyShift action_65
action_147 (44) = happyShift action_66
action_147 (53) = happyShift action_149
action_147 (20) = happyGoto action_92
action_147 (21) = happyGoto action_58
action_147 (22) = happyGoto action_59
action_147 (24) = happyGoto action_174
action_147 _ = happyFail

action_148 (27) = happyShift action_173
action_148 _ = happyFail

action_149 _ = happyReduce_58

action_150 (31) = happyShift action_172
action_150 _ = happyFail

action_151 (31) = happyShift action_171
action_151 _ = happyFail

action_152 (38) = happyShift action_170
action_152 _ = happyFail

action_153 (27) = happyShift action_60
action_153 (32) = happyShift action_61
action_153 (37) = happyShift action_62
action_153 (40) = happyShift action_63
action_153 (41) = happyShift action_64
action_153 (42) = happyShift action_65
action_153 (44) = happyShift action_66
action_153 (20) = happyGoto action_169
action_153 (21) = happyGoto action_58
action_153 (22) = happyGoto action_59
action_153 _ = happyFail

action_154 (27) = happyShift action_48
action_154 (32) = happyShift action_49
action_154 (42) = happyShift action_50
action_154 (14) = happyGoto action_168
action_154 (15) = happyGoto action_46
action_154 (16) = happyGoto action_47
action_154 _ = happyFail

action_155 _ = happyReduce_26

action_156 _ = happyReduce_41

action_157 (27) = happyShift action_27
action_157 (32) = happyShift action_28
action_157 (37) = happyShift action_29
action_157 (40) = happyShift action_30
action_157 (41) = happyShift action_31
action_157 (42) = happyShift action_32
action_157 (44) = happyShift action_33
action_157 (17) = happyGoto action_167
action_157 (18) = happyGoto action_25
action_157 (19) = happyGoto action_26
action_157 _ = happyFail

action_158 (27) = happyShift action_27
action_158 (32) = happyShift action_28
action_158 (37) = happyShift action_29
action_158 (40) = happyShift action_30
action_158 (41) = happyShift action_31
action_158 (42) = happyShift action_32
action_158 (44) = happyShift action_33
action_158 (17) = happyGoto action_166
action_158 (18) = happyGoto action_25
action_158 (19) = happyGoto action_26
action_158 _ = happyFail

action_159 (39) = happyShift action_165
action_159 _ = happyFail

action_160 (27) = happyShift action_27
action_160 (32) = happyShift action_28
action_160 (37) = happyShift action_29
action_160 (40) = happyShift action_30
action_160 (41) = happyShift action_31
action_160 (42) = happyShift action_32
action_160 (44) = happyShift action_33
action_160 (17) = happyGoto action_164
action_160 (18) = happyGoto action_25
action_160 (19) = happyGoto action_26
action_160 _ = happyFail

action_161 (27) = happyShift action_27
action_161 (32) = happyShift action_28
action_161 (37) = happyShift action_29
action_161 (40) = happyShift action_30
action_161 (41) = happyShift action_31
action_161 (42) = happyShift action_32
action_161 (44) = happyShift action_33
action_161 (17) = happyGoto action_163
action_161 (18) = happyGoto action_25
action_161 (19) = happyGoto action_26
action_161 _ = happyFail

action_162 _ = happyReduce_8

action_163 _ = happyReduce_35

action_164 _ = happyReduce_32

action_165 (27) = happyShift action_27
action_165 (32) = happyShift action_116
action_165 (37) = happyShift action_29
action_165 (40) = happyShift action_117
action_165 (41) = happyShift action_31
action_165 (42) = happyShift action_32
action_165 (44) = happyShift action_33
action_165 (53) = happyShift action_9
action_165 (17) = happyGoto action_190
action_165 (18) = happyGoto action_25
action_165 (19) = happyGoto action_26
action_165 (23) = happyGoto action_114
action_165 (25) = happyGoto action_137
action_165 _ = happyFail

action_166 _ = happyReduce_33

action_167 _ = happyReduce_34

action_168 (38) = happyShift action_189
action_168 _ = happyFail

action_169 (48) = happyShift action_188
action_169 _ = happyFail

action_170 _ = happyReduce_52

action_171 (27) = happyShift action_60
action_171 (32) = happyShift action_61
action_171 (37) = happyShift action_62
action_171 (40) = happyShift action_63
action_171 (41) = happyShift action_64
action_171 (42) = happyShift action_65
action_171 (44) = happyShift action_66
action_171 (20) = happyGoto action_187
action_171 (21) = happyGoto action_58
action_171 (22) = happyGoto action_59
action_171 _ = happyFail

action_172 (27) = happyShift action_60
action_172 (32) = happyShift action_61
action_172 (37) = happyShift action_62
action_172 (40) = happyShift action_63
action_172 (41) = happyShift action_64
action_172 (42) = happyShift action_65
action_172 (44) = happyShift action_66
action_172 (20) = happyGoto action_186
action_172 (21) = happyGoto action_58
action_172 (22) = happyGoto action_59
action_172 _ = happyFail

action_173 (39) = happyShift action_185
action_173 _ = happyFail

action_174 (33) = happyShift action_184
action_174 _ = happyFail

action_175 (27) = happyShift action_60
action_175 (32) = happyShift action_61
action_175 (37) = happyShift action_62
action_175 (40) = happyShift action_63
action_175 (41) = happyShift action_64
action_175 (42) = happyShift action_65
action_175 (44) = happyShift action_66
action_175 (20) = happyGoto action_183
action_175 (21) = happyGoto action_58
action_175 (22) = happyGoto action_59
action_175 _ = happyFail

action_176 (27) = happyShift action_60
action_176 (32) = happyShift action_61
action_176 (37) = happyShift action_62
action_176 (40) = happyShift action_63
action_176 (41) = happyShift action_64
action_176 (42) = happyShift action_65
action_176 (44) = happyShift action_66
action_176 (20) = happyGoto action_182
action_176 (21) = happyGoto action_58
action_176 (22) = happyGoto action_59
action_176 _ = happyFail

action_177 _ = happyReduce_10

action_178 _ = happyReduce_9

action_179 (31) = happyShift action_181
action_179 _ = happyFail

action_180 _ = happyReduce_54

action_181 (27) = happyShift action_27
action_181 (32) = happyShift action_28
action_181 (37) = happyShift action_29
action_181 (40) = happyShift action_30
action_181 (41) = happyShift action_31
action_181 (42) = happyShift action_32
action_181 (44) = happyShift action_33
action_181 (17) = happyGoto action_194
action_181 (18) = happyGoto action_25
action_181 (19) = happyGoto action_26
action_181 _ = happyFail

action_182 _ = happyReduce_46

action_183 _ = happyReduce_43

action_184 _ = happyReduce_59

action_185 (27) = happyShift action_60
action_185 (32) = happyShift action_147
action_185 (37) = happyShift action_62
action_185 (40) = happyShift action_148
action_185 (41) = happyShift action_64
action_185 (42) = happyShift action_65
action_185 (44) = happyShift action_66
action_185 (53) = happyShift action_149
action_185 (20) = happyGoto action_192
action_185 (21) = happyGoto action_58
action_185 (22) = happyGoto action_59
action_185 (24) = happyGoto action_145
action_185 (26) = happyGoto action_193
action_185 _ = happyFail

action_186 _ = happyReduce_44

action_187 _ = happyReduce_45

action_188 (27) = happyShift action_14
action_188 (32) = happyShift action_15
action_188 (34) = happyShift action_16
action_188 (42) = happyShift action_17
action_188 (43) = happyShift action_18
action_188 (45) = happyShift action_19
action_188 (46) = happyShift action_20
action_188 (49) = happyShift action_21
action_188 (50) = happyShift action_22
action_188 (51) = happyShift action_23
action_188 (10) = happyGoto action_191
action_188 (11) = happyGoto action_11
action_188 (12) = happyGoto action_12
action_188 (13) = happyGoto action_13
action_188 _ = happyFail

action_189 _ = happyReduce_12

action_190 (31) = happyShift action_157
action_190 _ = happyFail

action_191 _ = happyReduce_11

action_192 (31) = happyShift action_171
action_192 _ = happyFail

action_193 (31) = happyShift action_196
action_193 _ = happyFail

action_194 (35) = happyShift action_195
action_194 _ = happyFail

action_195 _ = happyReduce_23

action_196 (32) = happyShift action_198
action_196 (40) = happyShift action_199
action_196 (53) = happyShift action_149
action_196 (24) = happyGoto action_197
action_196 _ = happyFail

action_197 _ = happyReduce_57

action_198 (32) = happyShift action_198
action_198 (40) = happyShift action_199
action_198 (53) = happyShift action_149
action_198 (24) = happyGoto action_174
action_198 _ = happyFail

action_199 (27) = happyShift action_200
action_199 _ = happyFail

action_200 (39) = happyShift action_201
action_200 _ = happyFail

action_201 (27) = happyShift action_60
action_201 (32) = happyShift action_147
action_201 (37) = happyShift action_62
action_201 (40) = happyShift action_148
action_201 (41) = happyShift action_64
action_201 (42) = happyShift action_65
action_201 (44) = happyShift action_66
action_201 (53) = happyShift action_149
action_201 (20) = happyGoto action_144
action_201 (21) = happyGoto action_58
action_201 (22) = happyGoto action_59
action_201 (24) = happyGoto action_145
action_201 (26) = happyGoto action_193
action_201 _ = happyFail

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
	(HappyTerminal happy_var_2) `HappyStk`
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
	(HappyTerminal happy_var_2) `HappyStk`
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
	(HappyTerminal happy_var_2) `HappyStk`
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
	(HappyTerminal happy_var_2) `HappyStk`
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
	(HappyTerminal happy_var_2) `HappyStk`
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
	(HappyTerminal happy_var_2) `HappyStk`
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
	(HappyTerminal happy_var_2) `HappyStk`
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
	(HappyTerminal happy_var_2) `HappyStk`
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
	(HappyTerminal happy_var_2) `HappyStk`
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
	(HappyTerminal happy_var_2) `HappyStk`
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
	(HappyTerminal happy_var_2) `HappyStk`
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
	(HappyTerminal happy_var_2) `HappyStk`
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
	(HappyTerminal happy_var_2) `HappyStk`
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

happyNewToken action sts stk
	= lexer(\tk -> 
	let cont i = action i i tk (HappyState action) sts stk in
	case tk of {
	Token _ TEOF -> action 55 55 tk (HappyState action) sts stk;
	Token _ (TVar _) -> cont 27;
	Token _ (TProj _) -> cont 28;
	Token happy_dollar_dollar (TSym "=") -> cont 29;
	Token happy_dollar_dollar (TSym "◂") -> cont 30;
	Token happy_dollar_dollar (TSym ".") -> cont 31;
	Token happy_dollar_dollar (TSym "(") -> cont 32;
	Token happy_dollar_dollar (TSym ")") -> cont 33;
	Token happy_dollar_dollar (TSym "[") -> cont 34;
	Token happy_dollar_dollar (TSym "]") -> cont 35;
	Token happy_dollar_dollar (TSym ",") -> cont 36;
	Token happy_dollar_dollar (TSym "{") -> cont 37;
	Token happy_dollar_dollar (TSym "}") -> cont 38;
	Token happy_dollar_dollar (TSym ":") -> cont 39;
	Token happy_dollar_dollar (TSym "Π") -> cont 40;
	Token happy_dollar_dollar (TSym "∀") -> cont 41;
	Token happy_dollar_dollar (TSym "λ") -> cont 42;
	Token happy_dollar_dollar (TSym "Λ") -> cont 43;
	Token happy_dollar_dollar (TSym "ι") -> cont 44;
	Token happy_dollar_dollar (TSym "β") -> cont 45;
	Token happy_dollar_dollar (TSym "δ") -> cont 46;
	Token happy_dollar_dollar (TSym "·") -> cont 47;
	Token happy_dollar_dollar (TSym "-") -> cont 48;
	Token happy_dollar_dollar (TSym "ς") -> cont 49;
	Token happy_dollar_dollar (TSym "ρ") -> cont 50;
	Token happy_dollar_dollar (TSym "φ") -> cont 51;
	Token happy_dollar_dollar (TSym "≃") -> cont 52;
	Token happy_dollar_dollar (TSym "★") -> cont 53;
	Token happy_dollar_dollar (TSym "@") -> cont 54;
	_ -> happyError' tk
	})

happyError_ 55 tk = happyError' tk
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
