Modules
=======

Each options module starts with the following required attributes:

* `id` (string): ID of the module (e.g., `"arith"`)
* `name` (string): name of the module (e.g., `"Arithmetic Theory"`)

A module defines 0 or more options.

In general, each attribute/value pair is required to be in one line.
Comments start with # and are not allowed in attribute/value lines.

After parsing, a module is extended to have the following attributes:

* `id`: lower-case version of the parsed `id`
* `id_cap`: upper-case version of `id` (used for the `Holder{id_cap}` class)
* `filename`: base filename for generated files (`"{id}_options"`)
* `header`: generated header name (`"options/{filename}.h"`)

Options
=======

Options can be defined with the `[[option]]` tag, the required attributes for
an option are:

* `category` (string): one of `common`, `expert`, `regular`, or `undocumented`
* `type` (string): the C++ type of the option value

Optional attributes are:

* `name` (string): the option name used to access the option internally (`d_option.{module.id}().{name}`)
* `short` (string): short option name consisting of one character (no `-` prefix required)
* `long` (string): long option name (required if short is specified, no `--` prefix required). Long option names may have a suffix `=XXX` where `XXX` can be used to indicate the type of the option value, e.g., `=MODE`, `=LANG`, `=N`, ...
* `smt_name` (string): alternative name to access the option via `options::get()` and `options::set()`, and thereby via `(set-option ...)` and `(get-option ...)` from SMT-LIB
* `default` (string): default value, needs to be a valid C++ expression of type `type`
* `alternate` (bool, default `true`): if `true`, adds `--no-{long}` alternative option
* `mode` (list): used to define options whose type shall be an auto-generated enum (see example below)
* `handler` (string): alternate parsing routine for option types not covered by the default parsers, more details below
* `predicates` (list): custom validation function to check whether an option value is valid, more details below
* `includes` (list): additional header files required by handler or predicates
* `help` (string): documentation string (required, unless the `category` is `undocumented`)
* `help_mode` (string): documentation for the mode enum (required if `mode` is given)


Example:

    [[option]]
        name       = "outputLanguage"
        smt_name   = "output-language"
        category   = "common"
        short      = ""
        long       = "output-lang=LANG"
        type       = "OutputLanguage"
        default    = "language::output::LANG_AUTO"
        handler    = "stringToOutputLanguage"
        predicates = []
        includes   = ["options/language.h"]
        help       = "force output language (default is \"auto\"; see --output-lang help)"


Handler functions
-----------------

Custom handler functions are used to turn the option value from a `std::string` into the type specified by `type`.
Standard handler functions are provided for basic types (`std::string`, `bool`, integer types and floating point types) as well as enums specified by `mode`.
A custom handler function needs to be member function of `options::OptionsHandler` with signature `{type} {handler}(const std::string& option, const std::string& optionvalue)`, or alternatively `void {handler}(const std::string& option)` if the `type` is `void`.


Predicate functions
-------------------

Predicate functions are used to check whether an option value is valid after it has been parsed by a (standard or custom) handler function.
Like a handler function, a predicate function needs to be a member function of `options::OptionsHandler` with signature `void {predicate}(const std::string& option, {type} value)`. If the check fails, the predicate should raise an `OptionException`.
