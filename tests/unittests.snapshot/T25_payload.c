/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: /home/tahina/everest/master/kremlin/krml -ccopt -Ofast -drop FStar.Tactics.\* -drop FStar.Tactics -drop FStar.Reflection.\* -tmpdir out -I .. -bundle LowParse.\* -add-include "kremlin/internal/compat.h" -warn-error -9 ../../src/lowparse/LowParse_TestLib_Low_c.c -no-prefix Test kremlin/FStar_Pervasives_Native.krml kremlin/FStar_Pervasives.krml kremlin/FStar_Preorder.krml kremlin/FStar_Calc.krml kremlin/FStar_Squash.krml kremlin/FStar_Classical.krml kremlin/FStar_StrongExcludedMiddle.krml kremlin/FStar_FunctionalExtensionality.krml kremlin/FStar_List_Tot_Base.krml kremlin/FStar_List_Tot_Properties.krml kremlin/FStar_List_Tot.krml kremlin/FStar_Seq_Base.krml kremlin/FStar_Seq_Properties.krml kremlin/FStar_Seq.krml kremlin/FStar_Mul.krml kremlin/FStar_Math_Lib.krml kremlin/FStar_Math_Lemmas.krml kremlin/FStar_BitVector.krml kremlin/FStar_UInt.krml kremlin/FStar_UInt32.krml kremlin/FStar_Int.krml kremlin/FStar_Int16.krml kremlin/FStar_Range.krml kremlin/FStar_Reflection_Types.krml kremlin/FStar_Tactics_Types.krml kremlin/FStar_Tactics_Result.krml kremlin/FStar_Tactics_Effect.krml kremlin/FStar_Tactics_Util.krml kremlin/FStar_Reflection_Data.krml kremlin/FStar_Reflection_Const.krml kremlin/FStar_Char.krml kremlin/FStar_Exn.krml kremlin/FStar_Set.krml kremlin/FStar_Monotonic_Witnessed.krml kremlin/FStar_Ghost.krml kremlin/FStar_ErasedLogic.krml kremlin/FStar_PropositionalExtensionality.krml kremlin/FStar_PredicateExtensionality.krml kremlin/FStar_TSet.krml kremlin/FStar_Monotonic_Heap.krml kremlin/FStar_Heap.krml kremlin/FStar_ST.krml kremlin/FStar_All.krml kremlin/FStar_List.krml kremlin/FStar_String.krml kremlin/FStar_Order.krml kremlin/FStar_Reflection_Basic.krml kremlin/FStar_Reflection_Derived.krml kremlin/FStar_Tactics_Builtins.krml kremlin/FStar_Reflection_Formula.krml kremlin/FStar_Reflection_Derived_Lemmas.krml kremlin/FStar_Reflection.krml kremlin/FStar_Tactics_Derived.krml kremlin/FStar_Tactics_Logic.krml kremlin/FStar_Tactics.krml kremlin/FStar_Map.krml kremlin/FStar_Monotonic_HyperHeap.krml kremlin/FStar_Monotonic_HyperStack.krml kremlin/FStar_HyperStack.krml kremlin/FStar_HyperStack_ST.krml kremlin/FStar_Universe.krml kremlin/FStar_GSet.krml kremlin/FStar_ModifiesGen.krml kremlin/FStar_BigOps.krml kremlin/LowStar_Monotonic_Buffer.krml kremlin/LowStar_Buffer.krml kremlin/FStar_UInt8.krml kremlin/LowParse_Bytes.krml kremlin/LowParse_Spec_Base.krml kremlin/LowParse_Spec_Combinators.krml kremlin/LowParse_Spec_FLData.krml kremlin/Spec_Loops.krml kremlin/FStar_UInt64.krml kremlin/LowStar_BufferOps.krml kremlin/C_Loops.krml kremlin/LowParse_Math.krml kremlin/LowParse_Slice.krml kremlin/LowParse_Low_Base.krml kremlin/LowParse_Low_Combinators.krml kremlin/LowParse_Low_FLData.krml kremlin/FStar_Int64.krml kremlin/FStar_Int63.krml kremlin/FStar_Int32.krml kremlin/FStar_Int8.krml kremlin/FStar_UInt63.krml kremlin/FStar_UInt16.krml kremlin/FStar_Int_Cast.krml kremlin/FStar_HyperStack_All.krml kremlin/FStar_Kremlin_Endianness.krml kremlin/LowParse_BigEndian.krml kremlin/LowParse_Spec_Int_Aux.krml kremlin/LowParse_Spec_Int.krml kremlin/LowParse_Spec_BoundedInt.krml kremlin/LowStar_Modifies.krml kremlin/LowStar_ModifiesPat.krml kremlin/LowParse_BigEndianImpl_Base.krml kremlin/LowParse_BigEndianImpl_Low.krml kremlin/LowParse_Low_BoundedInt.krml kremlin/LowParse_Spec_SeqBytes_Base.krml kremlin/LowParse_Spec_DER.krml kremlin/LowParse_Spec_BCVLI.krml kremlin/LowParse_Spec_AllIntegers.krml kremlin/LowParse_Spec_VLData.krml kremlin/LowParse_Low_VLData.krml kremlin/LowParse_Spec_VLGen.krml kremlin/LowParse_Low_VLGen.krml kremlin/LowParse_Spec_Int_Unique.krml kremlin/LowParse_Low_Int_Aux.krml kremlin/LowParse_Low_Int.krml kremlin/LowParse_Low_DER.krml kremlin/LowParse_Low_BCVLI.krml kremlin/LowParse_Spec_List.krml kremlin/LowParse_Low_List.krml kremlin/LowParse_Spec_Array.krml kremlin/LowParse_Spec_VCList.krml kremlin/LowParse_Low_VCList.krml kremlin/LowParse_Spec_IfThenElse.krml kremlin/LowParse_Low_IfThenElse.krml kremlin/LowParse_TacLib.krml kremlin/LowParse_Spec_Enum.krml kremlin/LowParse_Spec_Sum.krml kremlin/LowParse_Low_Enum.krml kremlin/LowParse_Low_Sum.krml kremlin/LowParse_Low_Tac_Sum.krml kremlin/LowParse_Spec_Option.krml kremlin/LowParse_Low_Option.krml kremlin/FStar_Bytes.krml kremlin/LowParse_Bytes32.krml kremlin/LowParse_Spec_Bytes.krml kremlin/LowParse_Low_Bytes.krml kremlin/LowParse_Low_Array.krml kremlin/LowParse_Low.krml kremlin/LowParse_SLow_Base.krml kremlin/LowParse_SLow_Combinators.krml kremlin/LowParse_SLow_FLData.krml kremlin/LowParse_SLow_VLGen.krml kremlin/LowParse_BigEndianImpl_SLow.krml kremlin/LowParse_SLow_BoundedInt.krml kremlin/LowParse_SLow_Int_Aux.krml kremlin/LowParse_SLow_Int.krml kremlin/LowParse_SLow_DER.krml kremlin/LowParse_SLow_BCVLI.krml kremlin/LowParse_SLow_List.krml kremlin/LowParse_SLow_VCList.krml kremlin/LowParse_SLow_IfThenElse.krml kremlin/LowParse_SLow_Option.krml kremlin/LowParse_SLow_Enum.krml kremlin/LowParse_SLow_Sum.krml kremlin/LowParse_SLow_Tac_Enum.krml kremlin/LowParse_SLow_Tac_Sum.krml kremlin/LowParse_SLow_VLData.krml kremlin/LowParse_SLow_Bytes.krml kremlin/LowParse_SLow_Array.krml kremlin/LowParse_Spec_Tac_Combinators.krml kremlin/LowParse_SLow.krml kremlin/Tag2.krml kremlin/T15_body.krml kremlin/T3.krml kremlin/T5.krml kremlin/T9_b.krml kremlin/Amount.krml kremlin/Txout_scriptPubKey.krml kremlin/Txout.krml kremlin/Transaction_outputs.krml kremlin/Txin_scriptSig.krml kremlin/Sha256.krml kremlin/Txin.krml kremlin/Transaction_inputs.krml kremlin/Transaction.krml kremlin/Block_tx.krml kremlin/Block.krml kremlin/T25_bpayload.krml kremlin/FStar_Int128.krml kremlin/FStar_Int31.krml kremlin/FStar_UInt128.krml kremlin/FStar_UInt31.krml kremlin/FStar_Integers.krml kremlin/FStar_Printf.krml kremlin/Tagle.krml kremlin/T4.krml kremlin/T6le.krml kremlin/T24_y.krml kremlin/T24.krml kremlin/T25_payload.krml kremlin/T25.krml kremlin/T14_x.krml kremlin/T13_x.krml kremlin/T13.krml kremlin/T18_x_b.krml kremlin/T20.krml kremlin/T21.krml kremlin/C_Endianness.krml kremlin/C.krml kremlin/C_String.krml kremlin/T26.krml kremlin/Tag.krml kremlin/T16_x.krml kremlin/T16.krml kremlin/LowStar_ImmutableBuffer.krml kremlin/FStar_HyperStack_IO.krml kremlin/LowParse_TestLib_Low.krml kremlin/T18_x_a.krml kremlin/T33.krml kremlin/T19.krml kremlin/T1.krml kremlin/T17_x_b.krml kremlin/T22_body_b.krml kremlin/T12_z.krml kremlin/T12.krml kremlin/T2.krml kremlin/T7.krml kremlin/T8_z.krml kremlin/T27.krml kremlin/T14.krml kremlin/T32.krml kremlin/T29.krml kremlin/T36.krml kremlin/T10.krml kremlin/T17_x_a.krml kremlin/T17.krml kremlin/T15.krml kremlin/T35.krml kremlin/T22_body_a.krml kremlin/FStar_Float.krml kremlin/FStar_IO.krml kremlin/T18.krml kremlin/T23.krml kremlin/T9.krml kremlin/T8.krml kremlin/T28.krml kremlin/T6.krml kremlin/Test.krml kremlin/T30.krml kremlin/T11_z.krml kremlin/T34.krml kremlin/T11.krml kremlin/T31.krml kremlin/T22.krml -o test.exe
  F* version: 74c6d2a5
  KreMLin version: 1bd260eb
 */

#include "T25_payload.h"

FStar_Pervasives_Native_option__K___T24_t24_uint32_t
T25_payload_t25_payload_parser32(FStar_Bytes_bytes input)
{
  FStar_Pervasives_Native_option__K___uint8_t_uint32_t
  scrut0 = LowParse_SLow_Int_parse32_u8(input);
  FStar_Pervasives_Native_option__K___uint32_t_uint32_t scrut1;
  if (scrut0.tag == FStar_Pervasives_Native_None)
    scrut1 =
      (
        (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut0.tag == FStar_Pervasives_Native_Some)
  {
    uint32_t consumed_x = scrut0.v.snd;
    uint8_t x = scrut0.v.fst;
    uint8_t len1;
    if (x < (uint8_t)129U || x == (uint8_t)255U)
      len1 = (uint8_t)0U;
    else
      len1 = x - (uint8_t)128U;
    uint8_t tg1;
    if ((uint32_t)0U < (uint32_t)128U)
      tg1 = (uint8_t)(uint32_t)0U;
    else
    {
      uint8_t len_len;
      if ((uint32_t)0U < (uint32_t)256U)
        len_len = (uint8_t)1U;
      else if ((uint32_t)0U < (uint32_t)65536U)
        len_len = (uint8_t)2U;
      else if ((uint32_t)0U < (uint32_t)16777216U)
        len_len = (uint8_t)3U;
      else
        len_len = (uint8_t)4U;
      tg1 = (uint8_t)128U + len_len;
    }
    uint8_t l1;
    if (tg1 < (uint8_t)129U || tg1 == (uint8_t)255U)
      l1 = (uint8_t)0U;
    else
      l1 = tg1 - (uint8_t)128U;
    uint8_t tg2;
    if ((uint32_t)4294967295U < (uint32_t)128U)
      tg2 = (uint8_t)(uint32_t)4294967295U;
    else
    {
      uint8_t len_len;
      if ((uint32_t)4294967295U < (uint32_t)256U)
        len_len = (uint8_t)1U;
      else if ((uint32_t)4294967295U < (uint32_t)65536U)
        len_len = (uint8_t)2U;
      else if ((uint32_t)4294967295U < (uint32_t)16777216U)
        len_len = (uint8_t)3U;
      else
        len_len = (uint8_t)4U;
      tg2 = (uint8_t)128U + len_len;
    }
    uint8_t l2;
    if (tg2 < (uint8_t)129U || tg2 == (uint8_t)255U)
      l2 = (uint8_t)0U;
    else
      l2 = tg2 - (uint8_t)128U;
    if (len1 < l1 || l2 < len1)
      scrut1 =
        (
          (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else
    {
      FStar_Bytes_bytes input_ = FStar_Bytes_slice(input, consumed_x, FStar_Bytes_len(input));
      FStar_Pervasives_Native_option__K___uint32_t_uint32_t scrut0;
      if (x < (uint8_t)128U)
        scrut0 =
          (
            (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
              .tag = FStar_Pervasives_Native_Some,
              .v = { .fst = (uint32_t)x, .snd = (uint32_t)0U }
            }
          );
      else if (x == (uint8_t)128U || x == (uint8_t)255U)
        scrut0 =
          (
            (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
              .tag = FStar_Pervasives_Native_None
            }
          );
      else if (x == (uint8_t)129U)
      {
        FStar_Pervasives_Native_option__K___uint8_t_uint32_t
        scrut = LowParse_SLow_Int_parse32_u8(input_);
        if (scrut.tag == FStar_Pervasives_Native_None)
          scrut0 =
            (
              (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
                .tag = FStar_Pervasives_Native_None
              }
            );
        else if (scrut.tag == FStar_Pervasives_Native_Some)
        {
          uint32_t consumed = scrut.v.snd;
          uint8_t z = scrut.v.fst;
          if (z < (uint8_t)128U)
            scrut0 =
              (
                (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
                  .tag = FStar_Pervasives_Native_None
                }
              );
          else
            scrut0 =
              (
                (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = { .fst = (uint32_t)z, .snd = consumed }
                }
              );
        }
        else
          scrut0 =
            KRML_EABORT(FStar_Pervasives_Native_option__K___uint32_t_uint32_t,
              "unreachable (pattern matches are exhaustive in F*)");
      }
      else
      {
        uint8_t len2 = x - (uint8_t)128U;
        if (len2 == (uint8_t)2U)
        {
          FStar_Pervasives_Native_option__K___uint32_t_uint32_t
          scrut = LowParse_SLow_BoundedInt_parse32_bounded_integer_2(input_);
          if (scrut.tag == FStar_Pervasives_Native_None)
            scrut0 =
              (
                (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
                  .tag = FStar_Pervasives_Native_None
                }
              );
          else if (scrut.tag == FStar_Pervasives_Native_Some)
          {
            uint32_t consumed = scrut.v.snd;
            uint32_t y = scrut.v.fst;
            if (y < (uint32_t)256U)
              scrut0 =
                (
                  (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
                    .tag = FStar_Pervasives_Native_None
                  }
                );
            else
              scrut0 =
                (
                  (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = { .fst = y, .snd = consumed }
                  }
                );
          }
          else
            scrut0 =
              KRML_EABORT(FStar_Pervasives_Native_option__K___uint32_t_uint32_t,
                "unreachable (pattern matches are exhaustive in F*)");
        }
        else if (len2 == (uint8_t)3U)
        {
          FStar_Pervasives_Native_option__K___uint32_t_uint32_t
          scrut = LowParse_SLow_BoundedInt_parse32_bounded_integer_3(input_);
          if (scrut.tag == FStar_Pervasives_Native_None)
            scrut0 =
              (
                (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
                  .tag = FStar_Pervasives_Native_None
                }
              );
          else if (scrut.tag == FStar_Pervasives_Native_Some)
          {
            uint32_t consumed = scrut.v.snd;
            uint32_t y = scrut.v.fst;
            if (y < (uint32_t)65536U)
              scrut0 =
                (
                  (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
                    .tag = FStar_Pervasives_Native_None
                  }
                );
            else
              scrut0 =
                (
                  (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = { .fst = y, .snd = consumed }
                  }
                );
          }
          else
            scrut0 =
              KRML_EABORT(FStar_Pervasives_Native_option__K___uint32_t_uint32_t,
                "unreachable (pattern matches are exhaustive in F*)");
        }
        else
        {
          FStar_Pervasives_Native_option__K___uint32_t_uint32_t
          scrut = LowParse_SLow_BoundedInt_parse32_bounded_integer_4(input_);
          if (scrut.tag == FStar_Pervasives_Native_None)
            scrut0 =
              (
                (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
                  .tag = FStar_Pervasives_Native_None
                }
              );
          else if (scrut.tag == FStar_Pervasives_Native_Some)
          {
            uint32_t consumed = scrut.v.snd;
            uint32_t y = scrut.v.fst;
            if (y < (uint32_t)16777216U)
              scrut0 =
                (
                  (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
                    .tag = FStar_Pervasives_Native_None
                  }
                );
            else
              scrut0 =
                (
                  (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
                    .tag = FStar_Pervasives_Native_Some,
                    .v = { .fst = y, .snd = consumed }
                  }
                );
          }
          else
            scrut0 =
              KRML_EABORT(FStar_Pervasives_Native_option__K___uint32_t_uint32_t,
                "unreachable (pattern matches are exhaustive in F*)");
        }
      }
      if (scrut0.tag == FStar_Pervasives_Native_Some)
      {
        uint32_t consumed_y = scrut0.v.snd;
        uint32_t y = scrut0.v.fst;
        if (y < (uint32_t)0U || (uint32_t)4294967295U < y)
          scrut1 =
            (
              (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
                .tag = FStar_Pervasives_Native_None
              }
            );
        else
          scrut1 =
            (
              (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = { .fst = y, .snd = consumed_x + consumed_y }
              }
            );
      }
      else if (scrut0.tag == FStar_Pervasives_Native_None)
        scrut1 =
          (
            (FStar_Pervasives_Native_option__K___uint32_t_uint32_t){
              .tag = FStar_Pervasives_Native_None
            }
          );
      else
        scrut1 =
          KRML_EABORT(FStar_Pervasives_Native_option__K___uint32_t_uint32_t,
            "unreachable (pattern matches are exhaustive in F*)");
    }
  }
  else
    scrut1 =
      KRML_EABORT(FStar_Pervasives_Native_option__K___uint32_t_uint32_t,
        "unreachable (pattern matches are exhaustive in F*)");
  FStar_Pervasives_Native_option__K___T24_t24_uint32_t scrut2;
  if (scrut1.tag == FStar_Pervasives_Native_None)
    scrut2 =
      (
        (FStar_Pervasives_Native_option__K___T24_t24_uint32_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (scrut1.tag == FStar_Pervasives_Native_Some)
  {
    uint32_t consumed = scrut1.v.snd;
    uint32_t sz = scrut1.v.fst;
    FStar_Bytes_bytes input_ = FStar_Bytes_slice(input, consumed, FStar_Bytes_len(input));
    FStar_Pervasives_Native_option__K___T24_t24_uint32_t scrut0;
    if (FStar_Bytes_len(input_) < sz)
      scrut0 =
        (
          (FStar_Pervasives_Native_option__K___T24_t24_uint32_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else
    {
      FStar_Pervasives_Native_option__K___T24_t24_uint32_t
      scrut = T24_t24_parser32(FStar_Bytes_slice(input_, (uint32_t)0U, sz));
      if (scrut.tag == FStar_Pervasives_Native_Some)
      {
        uint32_t consumed1 = scrut.v.snd;
        T24_t24 v1 = scrut.v.fst;
        if (consumed1 == sz)
          scrut0 =
            (
              (FStar_Pervasives_Native_option__K___T24_t24_uint32_t){
                .tag = FStar_Pervasives_Native_Some,
                .v = { .fst = v1, .snd = consumed1 }
              }
            );
        else
          scrut0 =
            (
              (FStar_Pervasives_Native_option__K___T24_t24_uint32_t){
                .tag = FStar_Pervasives_Native_None
              }
            );
      }
      else if (scrut.tag == FStar_Pervasives_Native_None)
        scrut0 =
          (
            (FStar_Pervasives_Native_option__K___T24_t24_uint32_t){
              .tag = FStar_Pervasives_Native_None
            }
          );
      else
        scrut0 =
          KRML_EABORT(FStar_Pervasives_Native_option__K___T24_t24_uint32_t,
            "unreachable (pattern matches are exhaustive in F*)");
    }
    FStar_Pervasives_Native_option__K___T24_t24_uint32_t scrut;
    if (scrut0.tag == FStar_Pervasives_Native_Some)
    {
      uint32_t consumed1 = scrut0.v.snd;
      T24_t24 v1 = scrut0.v.fst;
      scrut =
        (
          (FStar_Pervasives_Native_option__K___T24_t24_uint32_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = v1, .snd = consumed1 }
          }
        );
    }
    else if (scrut0.tag == FStar_Pervasives_Native_None)
      scrut =
        (
          (FStar_Pervasives_Native_option__K___T24_t24_uint32_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else
      scrut =
        KRML_EABORT(FStar_Pervasives_Native_option__K___T24_t24_uint32_t,
          "unreachable (pattern matches are exhaustive in F*)");
    if (scrut.tag == FStar_Pervasives_Native_None)
      scrut2 =
        (
          (FStar_Pervasives_Native_option__K___T24_t24_uint32_t){
            .tag = FStar_Pervasives_Native_None
          }
        );
    else if (scrut.tag == FStar_Pervasives_Native_Some)
    {
      uint32_t consumed_ = scrut.v.snd;
      T24_t24 x = scrut.v.fst;
      scrut2 =
        (
          (FStar_Pervasives_Native_option__K___T24_t24_uint32_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .fst = x, .snd = consumed + consumed_ }
          }
        );
    }
    else
      scrut2 =
        KRML_EABORT(FStar_Pervasives_Native_option__K___T24_t24_uint32_t,
          "unreachable (pattern matches are exhaustive in F*)");
  }
  else
    scrut2 =
      KRML_EABORT(FStar_Pervasives_Native_option__K___T24_t24_uint32_t,
        "unreachable (pattern matches are exhaustive in F*)");
  if (scrut2.tag == FStar_Pervasives_Native_Some)
  {
    uint32_t consumed = scrut2.v.snd;
    T24_t24 v1 = scrut2.v.fst;
    return
      (
        (FStar_Pervasives_Native_option__K___T24_t24_uint32_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = { .fst = v1, .snd = consumed }
        }
      );
  }
  else
    return
      (
        (FStar_Pervasives_Native_option__K___T24_t24_uint32_t){
          .tag = FStar_Pervasives_Native_None
        }
      );
}

FStar_Bytes_bytes T25_payload_t25_payload_serializer32(T24_t24 input)
{
  T24_t24 x = input;
  FStar_Bytes_bytes sp = T24_t24_serializer32(x);
  uint32_t len1 = FStar_Bytes_len(sp);
  uint8_t x1;
  if (len1 < (uint32_t)128U)
    x1 = (uint8_t)len1;
  else
  {
    uint8_t len_len;
    if (len1 < (uint32_t)256U)
      len_len = (uint8_t)1U;
    else if (len1 < (uint32_t)65536U)
      len_len = (uint8_t)2U;
    else if (len1 < (uint32_t)16777216U)
      len_len = (uint8_t)3U;
    else
      len_len = (uint8_t)4U;
    x1 = (uint8_t)128U + len_len;
  }
  FStar_Bytes_bytes sx = FStar_Bytes_create((uint32_t)1U, x1);
  FStar_Bytes_bytes ite;
  if (x1 < (uint8_t)128U)
    ite = sx;
  else if (x1 == (uint8_t)129U)
    ite = FStar_Bytes_append(sx, FStar_Bytes_create((uint32_t)1U, (uint8_t)len1));
  else if (x1 == (uint8_t)130U)
    ite = FStar_Bytes_append(sx, LowParse_SLow_BoundedInt_serialize32_bounded_integer_2(len1));
  else if (x1 == (uint8_t)131U)
    ite = FStar_Bytes_append(sx, LowParse_SLow_BoundedInt_serialize32_bounded_integer_3(len1));
  else
    ite = FStar_Bytes_append(sx, LowParse_SLow_BoundedInt_serialize32_bounded_integer_4(len1));
  return FStar_Bytes_append(ite, sp);
}

uint32_t T25_payload_t25_payload_size32(T24_t24 input)
{
  uint32_t sp = T24_t24_size32(input);
  uint32_t ite;
  if (sp < (uint32_t)128U)
    ite = (uint32_t)1U;
  else if (sp < (uint32_t)256U)
    ite = (uint32_t)2U;
  else if (sp < (uint32_t)65536U)
    ite = (uint32_t)3U;
  else if (sp < (uint32_t)16777216U)
    ite = (uint32_t)4U;
  else
    ite = (uint32_t)5U;
  return ite + sp;
}

uint32_t T25_payload_t25_payload_validator(LowParse_Slice_slice input, uint32_t pos)
{
  uint32_t v10;
  if (input.len - pos < (uint32_t)1U)
    v10 = LOWPARSE_LOW_BASE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    v10 = pos + (uint32_t)1U;
  uint32_t n1;
  if (LOWPARSE_LOW_BASE_VALIDATOR_MAX_LENGTH < v10)
    n1 = v10;
  else
  {
    uint8_t x = LowParse_Low_Int_read_u8(input, pos);
    uint8_t len1;
    if (x < (uint8_t)129U || x == (uint8_t)255U)
      len1 = (uint8_t)0U;
    else
      len1 = x - (uint8_t)128U;
    uint8_t tg1;
    if ((uint32_t)0U < (uint32_t)128U)
      tg1 = (uint8_t)(uint32_t)0U;
    else
    {
      uint8_t len_len;
      if ((uint32_t)0U < (uint32_t)256U)
        len_len = (uint8_t)1U;
      else if ((uint32_t)0U < (uint32_t)65536U)
        len_len = (uint8_t)2U;
      else if ((uint32_t)0U < (uint32_t)16777216U)
        len_len = (uint8_t)3U;
      else
        len_len = (uint8_t)4U;
      tg1 = (uint8_t)128U + len_len;
    }
    uint8_t l1;
    if (tg1 < (uint8_t)129U || tg1 == (uint8_t)255U)
      l1 = (uint8_t)0U;
    else
      l1 = tg1 - (uint8_t)128U;
    uint8_t tg2;
    if ((uint32_t)4294967295U < (uint32_t)128U)
      tg2 = (uint8_t)(uint32_t)4294967295U;
    else
    {
      uint8_t len_len;
      if ((uint32_t)4294967295U < (uint32_t)256U)
        len_len = (uint8_t)1U;
      else if ((uint32_t)4294967295U < (uint32_t)65536U)
        len_len = (uint8_t)2U;
      else if ((uint32_t)4294967295U < (uint32_t)16777216U)
        len_len = (uint8_t)3U;
      else
        len_len = (uint8_t)4U;
      tg2 = (uint8_t)128U + len_len;
    }
    uint8_t l2;
    if (tg2 < (uint8_t)129U || tg2 == (uint8_t)255U)
      l2 = (uint8_t)0U;
    else
      l2 = tg2 - (uint8_t)128U;
    if (len1 < l1 || l2 < len1)
      n1 = LOWPARSE_LOW_BASE_VALIDATOR_ERROR_GENERIC;
    else
    {
      uint32_t v20;
      if (x < (uint8_t)128U)
        v20 = v10;
      else if (x == (uint8_t)128U || x == (uint8_t)255U)
        v20 = LOWPARSE_LOW_BASE_VALIDATOR_ERROR_GENERIC;
      else if (x == (uint8_t)129U)
      {
        uint32_t v2;
        if (input.len - v10 < (uint32_t)1U)
          v2 = LOWPARSE_LOW_BASE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
        else
          v2 = v10 + (uint32_t)1U;
        if (LOWPARSE_LOW_BASE_VALIDATOR_MAX_LENGTH < v2)
          v20 = v2;
        else
        {
          uint8_t z = LowParse_Low_Int_read_u8(input, v10);
          if (z < (uint8_t)128U)
            v20 = LOWPARSE_LOW_BASE_VALIDATOR_ERROR_GENERIC;
          else
            v20 = v2;
        }
      }
      else
      {
        uint8_t len2 = x - (uint8_t)128U;
        if (len2 == (uint8_t)2U)
        {
          uint32_t v2;
          if (input.len - v10 < (uint32_t)2U)
            v2 = LOWPARSE_LOW_BASE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
          else
            v2 = v10 + (uint32_t)2U;
          if (LOWPARSE_LOW_BASE_VALIDATOR_MAX_LENGTH < v2)
            v20 = v2;
          else
          {
            uint32_t y = LowParse_Low_BoundedInt_read_bounded_integer_2(input, v10);
            if (y < (uint32_t)256U)
              v20 = LOWPARSE_LOW_BASE_VALIDATOR_ERROR_GENERIC;
            else
              v20 = v2;
          }
        }
        else if (len2 == (uint8_t)3U)
        {
          uint32_t v2;
          if (input.len - v10 < (uint32_t)3U)
            v2 = LOWPARSE_LOW_BASE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
          else
            v2 = v10 + (uint32_t)3U;
          if (LOWPARSE_LOW_BASE_VALIDATOR_MAX_LENGTH < v2)
            v20 = v2;
          else
          {
            uint32_t y = LowParse_Low_BoundedInt_read_bounded_integer_3(input, v10);
            if (y < (uint32_t)65536U)
              v20 = LOWPARSE_LOW_BASE_VALIDATOR_ERROR_GENERIC;
            else
              v20 = v2;
          }
        }
        else
        {
          uint32_t v2;
          if (input.len - v10 < (uint32_t)4U)
            v2 = LOWPARSE_LOW_BASE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
          else
            v2 = v10 + (uint32_t)4U;
          if (LOWPARSE_LOW_BASE_VALIDATOR_MAX_LENGTH < v2)
            v20 = v2;
          else
          {
            uint32_t y = LowParse_Low_BoundedInt_read_bounded_integer_4(input, v10);
            if (y < (uint32_t)16777216U)
              v20 = LOWPARSE_LOW_BASE_VALIDATOR_ERROR_GENERIC;
            else
              v20 = v2;
          }
        }
      }
      if (LOWPARSE_LOW_BASE_VALIDATOR_MAX_LENGTH < v20)
        n1 = v20;
      else
      {
        uint32_t y;
        if (x < (uint8_t)128U)
          y = (uint32_t)x;
        else if (x == (uint8_t)129U)
        {
          uint8_t z = LowParse_Low_Int_read_u8(input, v10);
          y = (uint32_t)z;
        }
        else
        {
          uint8_t len2 = x - (uint8_t)128U;
          if (len2 == (uint8_t)2U)
          {
            uint32_t res = LowParse_Low_BoundedInt_read_bounded_integer_2(input, v10);
            y = res;
          }
          else if (len2 == (uint8_t)3U)
          {
            uint32_t res = LowParse_Low_BoundedInt_read_bounded_integer_3(input, v10);
            y = res;
          }
          else
          {
            uint32_t res = LowParse_Low_BoundedInt_read_bounded_integer_4(input, v10);
            y = res;
          }
        }
        if (y < (uint32_t)0U || (uint32_t)4294967295U < y)
          n1 = LOWPARSE_LOW_BASE_VALIDATOR_ERROR_GENERIC;
        else
          n1 = v20;
      }
    }
  }
  if (LOWPARSE_LOW_BASE_VALIDATOR_MAX_LENGTH < n1)
    return n1;
  else
  {
    uint32_t v1 = pos + (uint32_t)1U;
    uint8_t x = LowParse_Low_Int_read_u8(input, pos);
    uint8_t len1;
    if (x < (uint8_t)129U || x == (uint8_t)255U)
      len1 = (uint8_t)0U;
    else
      len1 = x - (uint8_t)128U;
    uint32_t y;
    if (x < (uint8_t)128U)
      y = (uint32_t)x;
    else if (x == (uint8_t)129U)
    {
      uint8_t z = LowParse_Low_Int_read_u8(input, v1);
      y = (uint32_t)z;
    }
    else
    {
      uint8_t len2 = x - (uint8_t)128U;
      if (len2 == (uint8_t)2U)
      {
        uint32_t res = LowParse_Low_BoundedInt_read_bounded_integer_2(input, v1);
        y = res;
      }
      else if (len2 == (uint8_t)3U)
      {
        uint32_t res = LowParse_Low_BoundedInt_read_bounded_integer_3(input, v1);
        y = res;
      }
      else
      {
        uint32_t res = LowParse_Low_BoundedInt_read_bounded_integer_4(input, v1);
        y = res;
      }
    }
    uint32_t len10 = y;
    if (input.len - n1 < len10)
      return LOWPARSE_LOW_BASE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    else
    {
      uint32_t
      pos_ =
        T24_t24_validator(((LowParse_Slice_slice){ .base = input.base, .len = n1 + len10 }),
          n1);
      if (LOWPARSE_LOW_BASE_VALIDATOR_MAX_LENGTH < pos_)
        if (pos_ == LOWPARSE_LOW_BASE_VALIDATOR_ERROR_NOT_ENOUGH_DATA)
          return LOWPARSE_LOW_BASE_VALIDATOR_ERROR_GENERIC;
        else
          return pos_;
      else if (pos_ - n1 != len10)
        return LOWPARSE_LOW_BASE_VALIDATOR_ERROR_GENERIC;
      else
        return pos_;
    }
  }
}

uint32_t T25_payload_t25_payload_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  uint32_t v10 = pos + (uint32_t)1U;
  uint8_t x0 = LowParse_Low_Int_read_u8(input, pos);
  uint8_t len10;
  if (x0 < (uint8_t)129U || x0 == (uint8_t)255U)
    len10 = (uint8_t)0U;
  else
    len10 = x0 - (uint8_t)128U;
  uint32_t n1;
  if (x0 < (uint8_t)128U)
    n1 = v10;
  else
    n1 = v10 + (uint32_t)(x0 - (uint8_t)128U);
  uint32_t v1 = pos + (uint32_t)1U;
  uint8_t x = LowParse_Low_Int_read_u8(input, pos);
  uint8_t len1;
  if (x < (uint8_t)129U || x == (uint8_t)255U)
    len1 = (uint8_t)0U;
  else
    len1 = x - (uint8_t)128U;
  uint32_t y;
  if (x < (uint8_t)128U)
    y = (uint32_t)x;
  else if (x == (uint8_t)129U)
  {
    uint8_t z = LowParse_Low_Int_read_u8(input, v1);
    y = (uint32_t)z;
  }
  else
  {
    uint8_t len2 = x - (uint8_t)128U;
    if (len2 == (uint8_t)2U)
    {
      uint32_t res = LowParse_Low_BoundedInt_read_bounded_integer_2(input, v1);
      y = res;
    }
    else if (len2 == (uint8_t)3U)
    {
      uint32_t res = LowParse_Low_BoundedInt_read_bounded_integer_3(input, v1);
      y = res;
    }
    else
    {
      uint32_t res = LowParse_Low_BoundedInt_read_bounded_integer_4(input, v1);
      y = res;
    }
  }
  uint32_t len11 = y;
  return n1 + len11;
}

uint32_t T25_payload_t25_payload_accessor(LowParse_Slice_slice input, uint32_t pos)
{
  uint32_t v1 = pos + (uint32_t)1U;
  uint8_t x = LowParse_Low_Int_read_u8(input, pos);
  uint8_t len1;
  if (x < (uint8_t)129U || x == (uint8_t)255U)
    len1 = (uint8_t)0U;
  else
    len1 = x - (uint8_t)128U;
  if (x < (uint8_t)128U)
    return v1;
  else
    return v1 + (uint32_t)(x - (uint8_t)128U);
}

