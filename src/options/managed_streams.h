/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrappers to handle memory management of streams.
 *
 * This file contains wrappers to handle special cases of managing memory
 * related to streams stored in options.
 */

#include "cvc5_public.h"

#ifndef CVC5__OPTIONS__MANAGED_STREAMS_H
#define CVC5__OPTIONS__MANAGED_STREAMS_H

#include <memory>
#include <ostream>

#include "options/options_public.h"

namespace cvc5 {

namespace detail {
std::ostream* openOStream(const std::string& value);
std::istream* openIStream(const std::string& value);
}

template <typename Stream>
class ManagedStream
{
  virtual Stream* defaultValue() const = 0;
  virtual bool specialCases(const std::string& value) = 0;

  Stream* getPtr() const {
      if (d_stream) return d_stream.get();
      return defaultValue();
  }

 public:
  ManagedStream() {}
  virtual ~ManagedStream() {}

  void open(const std::string& value)
  {
      if (specialCases(value)) return;
      if constexpr(std::is_same<Stream, std::ostream>::value)
      {
          d_stream.reset(detail::openOStream(value));
      } else if constexpr(std::is_same<Stream, std::istream>::value) {
          d_stream.reset(detail::openIStream(value));
      }
  }

  Stream& operator*() const {
      return *getPtr();
  }
  Stream* operator->() const {
      return getPtr();
  }
  operator Stream&() const {
      return *getPtr();
  }
  operator Stream*() const {
      return getPtr();
  }
  
  protected:
  std::shared_ptr<Stream> d_stream;
};

template <typename Stream>
std::ostream& operator<<(std::ostream& os, const ManagedStream<Stream>& ms)
{
    return os << "ManagedStream";
}

class ManagedErr: public ManagedStream<std::ostream>
{
  std::ostream* defaultValue() const override final;
  bool specialCases(const std::string& value) override final;
};

class ManagedIn: public ManagedStream<std::istream>
{
  std::istream* defaultValue() const override final;
  bool specialCases(const std::string& value) override final;
};

class ManagedOut: public ManagedStream<std::ostream>
{
  std::ostream* defaultValue() const override final;
  bool specialCases(const std::string& value) override final;
};

}  // namespace cvc5

#endif /* CVC5__OPTIONS__MANAGED_STREAMS_H */
