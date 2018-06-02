module TysWiredIn where

import BasicTypes( Boxity )
import {-# SOURCE #-} TyCon      ( TyCon )
import {-# SOURCE #-} TyCoRep    (Type, Kind)

intTy :: Type
mkTupleTy :: Boxity -> [Type] -> Type

listTyCon :: TyCon
typeNatKind, typeSymbolKind :: Type
mkBoxedTupleTy :: [Type] -> Type

liftedTypeKind :: Kind
constraintKind :: Kind

runtimeRepTyCon, vecCountTyCon, vecElemTyCon :: TyCon
runtimeRepTy :: Type
ptrRepLiftedTy :: Type

ptrRepUnliftedDataConTyCon, vecRepDataConTyCon :: TyCon

voidRepDataConTy, intRepDataConTy,
  wordRepDataConTy, int64RepDataConTy, word64RepDataConTy, addrRepDataConTy,
  floatRepDataConTy, doubleRepDataConTy, unboxedTupleRepDataConTy,
  refRepDataConTy, refURepDataConTy :: Type

vec2DataConTy, vec4DataConTy, vec8DataConTy, vec16DataConTy, vec32DataConTy,
  vec64DataConTy :: Type

int8ElemRepDataConTy, int16ElemRepDataConTy, int32ElemRepDataConTy,
  int64ElemRepDataConTy, word8ElemRepDataConTy, word16ElemRepDataConTy,
  word32ElemRepDataConTy, word64ElemRepDataConTy, floatElemRepDataConTy,
  doubleElemRepDataConTy :: Type
