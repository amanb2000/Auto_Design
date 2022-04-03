using Logging
using Combinatorics

@info "Hello, world"


include("../lib/DesignTools.jl")

## Helper function: Get single character functional dependencies
function get_set_dependencies(S_str::Set)
    """Given a set of pairs of STRINGS `S_str`, we split each string into
    sets of 1-character-long strings and return the new dependency set.
    """
    S = Set()
    for pair_ in S_str
        lhs = pair_[1]
        rhs = pair_[2]
        # lhs_substrings = split(lhs, "")
        # lhs_strings = [String(l) for l in lhs_substrings]
        lhs_strings = string_to_charset(lhs)

        rhs_substrings = split(rhs, "")
        rhs_strings = [String(r) for r in rhs_substrings]
        rhs_strings = string_to_charset(rhs)

        push!(S, Set(lhs_strings) => Set(rhs_strings))
    end
    return S
end

function string_to_charset(St::String)
    substrings = split(St, "")
    strings = [String(l) for l in substrings]
    return Set(strings)
end

## Testing projection
FD_str = Set([
    "ABE" => "CF",
    "DF" => "BD",
    "C" => "DF",
    "E" => "A",
    "AF" => "B"
])
# FD_str = Set([
#     "A" => "B",
#     "B" => "C"
# ])
FD = get_set_dependencies(FD_str)

# Y = Set(["A", "B", "C"])
# potential_dependence = string_to_charset("A") => string_to_charset("B")
# FD_min = minimal_basis(FD)
# @info FD_min

L = Set(["C", "D", "E", "F"])

FD_L = project(FD, L)
FD_L = minimal_basis(FD_L)
println("\nFinal minimum basis in L")
for pair in FD_L
    println(pair)
end
## MB Question 2
 # Find the minimal basis for S as defined below:

FD_str = Set([
 "ABF" => "G",
 "BC" => "H",
 "BCH" => "EG",
 "BE" => "GH"
])
FD = get_set_dependencies(FD_str)
FD_min = minimal_basis(FD)
println("\nFinal minimum basis:")
for pair in FD_min
    println(pair)
end
