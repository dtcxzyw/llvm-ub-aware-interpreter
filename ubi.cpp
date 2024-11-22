// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2024 Yingwei Zheng
// This file is licensed under the Apache-2.0 License.
// See the LICENSE file for more information.

#include "ubi.h"
#include <cassert>
#include <utility>

ImmUBReporter::ImmUBReporter() : Out(errs()) { Out << "\nUB triggered: "; }
[[noreturn]] ImmUBReporter::~ImmUBReporter() {
  Out << "\nExited with immediate UB.\n";
  Out.flush();
  std::exit(EXIT_FAILURE);
}

MemObject::~MemObject() { Manager.erase(Address.getZExtValue()); }
void MemObject::verifyMemAccess(const APInt &Offset, const size_t AccessSize,
                                size_t Alignment) {
  auto NewAddr = Address + Offset;
  if (NewAddr.countr_zero() < Log2_64(Alignment))
    ImmUBReporter() << "Unaligned mem op";
  if ((Offset + AccessSize).ugt(Data.size()))
    ImmUBReporter() << "Out of bound mem op, bound = " << Data.size()
                    << ", access range = [" << Offset << ", "
                    << Offset + AccessSize << ')';
}
void MemObject::store(size_t Offset, const APInt &C) {
  constexpr uint32_t Scale = sizeof(APInt::WordType);
  const size_t Size = alignTo(C.getBitWidth(), 8) / 8;
  uint32_t WriteCnt = 0;
  std::byte *WritePos = Data.data() + Offset;
  for (uint32_t I = 0; I != C.getNumWords(); ++I) {
    auto Word = C.getRawData()[I];
    if (WriteCnt + Scale <= Size) {
      memcpy(&WritePos[WriteCnt], &Word, sizeof(Word));
      WriteCnt += Scale;
      if (WriteCnt == Size)
        return;
    } else {
      for (auto J = 0; J != Scale; ++J) {
        WritePos[WriteCnt] = static_cast<std::byte>(Word & 255);
        Word >>= 8;
        if (++WriteCnt == Size)
          return;
      }
    }
  }
}
APInt MemObject::load(size_t Offset, size_t Bits) const {
  APInt Res = APInt::getZero(alignTo(Bits, 8));
  constexpr uint32_t Scale = sizeof(APInt::WordType);
  const size_t Size = Res.getBitWidth() / 8;
  uint32_t ReadCnt = 0;
  const std::byte *ReadPos = Data.data() + Offset;
  for (uint32_t I = 0; I != Res.getNumWords(); ++I) {
    auto &Word = const_cast<APInt::WordType &>(Res.getRawData()[I]);
    if (ReadCnt + Scale <= Size) {
      memcpy(&Word, &ReadPos[ReadCnt], sizeof(Word));
      ReadPos += Scale;
      if (ReadCnt == Size)
        break;
    } else {
      for (auto J = 0; J != Scale; ++J) {
        Word |= static_cast<APInt::WordType>(ReadPos[ReadCnt]) << (J * 8);
        if (++ReadCnt == Size)
          break;
      }
      if (ReadCnt == Size)
        break;
    }
  }
  return Res.trunc(Bits);
}
void MemObject::dumpName(raw_ostream &Out) {
  Out << (IsLocal ? '%' : '@') << Name;
}
void MemObject::dumpRef(raw_ostream &Out) {
  Out << '[' << (IsLocal ? '%' : '@') << Name << "(Addr = " << Address << ", "
      << "Size = " << Data.size() << ']';
}

MemoryManager::MemoryManager(const DataLayout &DL, PointerType *Ty)
    : PtrBitWidth(DL.getTypeSizeInBits(Ty)) {
  assert(DL.getTypeSizeInBits(Ty) ==
         DL.getIndexSizeInBits(Ty->getAddressSpace()));
}
std::shared_ptr<MemObject> MemoryManager::create(std::string Name, bool IsLocal,
                                                 size_t Size,
                                                 size_t Alignment) {
  AllocatedMem = alignTo(AllocatedMem, Alignment);
  auto Address = APInt(PtrBitWidth, AllocatedMem);
  AllocatedMem += Size + Padding;
  auto Obj = std::make_shared<MemObject>(*this, std::move(Name), IsLocal,
                                         std::move(Address), Size);
  AddressMap.emplace(Address.getZExtValue(), Obj.get());
  return std::move(Obj);
}
SingleValue MemoryManager::lookupPointer(const APInt &Addr) const {
  if (auto Iter = AddressMap.upper_bound(Addr.getZExtValue());
      Iter != AddressMap.begin()) {
    auto *MO = std::prev(Iter)->second;
    if (MO->address().ule(Addr) && Addr.ule(MO->address() + MO->size())) {
      return SingleValue{Pointer{MO->shared_from_this(), Addr - MO->address()}};
    }
  }

  return SingleValue{Pointer{std::weak_ptr<MemObject>{},
                             APInt::getZero(Addr.getBitWidth()), Addr, 0}};
}
