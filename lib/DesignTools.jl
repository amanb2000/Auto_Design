## Attribute closure algorithm
function attribute_closure(Y::Set{String}, S::Set; verbose::Bool=false)
    """Given a set of attributes `Y` and some set of functional dependencies
    `S`, returns the closure of attributes `Y`.
    """
    Y_plus = deepcopy(Y)
    did_change = true
    while did_change
        did_change = false
        for pair_ in S
            lhs = pair_[1]
            rhs = pair_[2]
            if verbose
                println("LHS: ", lhs)
                println("RHS: ", rhs)
                println("Y_plus: ", Y_plus)
            end
            if issubset(lhs, Y_plus)
                if verbose
                    println("LHS ", lhs," is a subset of Y_plus ", Y_plus)
                end
                if !issubset(rhs,Y_plus)
                    if verbose
                        println("RHS ", rhs, " is not in Y_plus! Adding it to Y_plus...")
                    end
                    did_change = true
                    union!(Y_plus, rhs)
                    break
                end
            end
        end
    end

    return Y_plus
end

## Closure test: Function to see if a given functional dependence follows
 # from a set of attributes `S`

function fd_follows(S::Set, FD::Pair{Set{String},Set{String}})
    """Given a potential functional dependence FD, we return
    `true` if it is implied by the functional dependencies in `S`
    and `false` if not.
    """
    LHS = FD[1]
    RHS = FD[2]

    Y_plus = attribute_closure(LHS, S)
    return issubset(RHS, Y_plus)
end

## Projection algorithm: Given some set of functional dependencies  and a
 # subset of attributes `L`, we return all the FD's that follow from the
 # original set that ONLY concern attributes in `L`
function project(S::Set, L::Set{String}; verbose::Bool=false)
    """Project the functional dependencies in `S` onto the attributes
    in `L`.
    """
    T = Set()

    L_list = [el for el in L]

    L_powerset = collect(powerset(L_list))
    for X in L_powerset
        X_set = Set(X)
        X_set_closure = attribute_closure(X_set, S)

        if verbose
            println("X_set is ", X_set, " with closure ", X_set_closure)
        end

        for A in X_set_closure # a is a string representing 1 attribute
            if A in L && !(A in X)
                if verbose
                    println("\tAdding attribute ", A, " because it is in `L` and NOT in `X`")
                end

                push!(T, Set(X)=>Set([A]))
            end
        end
        # @info X_set X_set_closure
    end

    return T
end

## Minimal basis: A minimal basis will have 3 important properties,
 # 1. No redundant functional dependencies.
 # 2. No functional dependencies with unnecessary attributeson the LHS.
 # 3. All RHS are single attributes.

function minimal_basis(S::Set; verbose::Bool=false)
    """Takes `S`, a set of pairs of sets, and returns the minimal basis.
    S has the form Set([
            Set(["A", "B"]) => Set(["C"]),
            ...
        ])
    """
    S_min::Set{Pair{ Set{String}, Set{String} }} = Set()
    # 1: Split the right hand side of each pair in S
    for pair_ in S
        lhs = pair_[1]
        rhs = pair_[2]

        for attribute in rhs
            # println(typeof(attribute))
            push!(S_min, lhs => Set([attribute]))
        end
    end
    if verbose
        println("\nAfter splitting all attributes, S_min is: ")
        for pair in S_min
            println("\t",pair)
        end

        println("\nBeginning step 2: removing LHS attributes where possible.")
    end


    # 2: Removing attributes where possible.
    did_remove = true # flag: whether we were able to remove anything.
    while did_remove
        did_remove = false
        # Looping through S_min's attributes, looking for |LHS| ≥ 2
        for pair_ in S_min
            lhs = pair_[1]
            rhs = pair_[2]

            if(length(lhs) >= 2)
                for remove_this in lhs
                    new_lhs = setdiff(lhs, Set([remove_this]) )
                    new_pair = new_lhs=>rhs
                    is_known = new_pair in S_min

                    if (!is_known && fd_follows(S_min, new_lhs=>rhs)) # it does follow...
                        if verbose
                            println("\tAble to remove attribute ", remove_this, " from ", lhs=>rhs)
                            println("\t\tAdding replacement ", new_lhs=>rhs)
                        end
                        push!(S_min, new_lhs=>rhs)
                        S_min = setdiff(S_min, Set([lhs=>rhs]))
                        # pop!(S_min, lhs=>rhs)
                        did_remove = true
                        break
                    elseif is_known && fd_follows(S_min, new_lhs=>rhs)
                        if verbose
                            println("\tStronger version of ", lhs=>rhs, " is already known: ", new_lhs=>rhs)
                            println("\t\tDeleting ", lhs=>rhs)
                        end
                        pop!(S_min, lhs=>rhs)
                        did_remove = true
                        break
                    end
                end
            end
            if did_remove
                break
            end
        end
    end

    if verbose
        println("\nAfter removing redundant LHS terms, S_min is: ")
        for pair in S_min
            println("\t",pair)
        end
        println("\nBeginning step 3: removing redundant FD's...")
    end


    # 3: Removing redundant FD's
    did_remove = true
    while did_remove
        did_remove = false
        for pair_ in S_min
            S_min_potential = setdiff(S_min, Set([pair_]))
            if fd_follows(S_min_potential, pair_)
                if verbose
                    println("\tAble to remove ",pair_," without changing FD's!")
                end
                pop!(S_min, pair_)
                did_remove = true
                break
            end
        end
    end
    return S_min
end

## BCNF <==> the closure of each LHS is the set of all attributes for all
 # LHS ∈ nontrivial_FDs
function is_BCNF(All_FDs::Set, specific_FDs::Set, attributes::Set; verbose::Bool=false)
    """Given some set of non-trivial `specific_FDs` and
    a list of all FDs `All_FDs` to check against, and
    the list of all attributes in the table, return
    whether or not the relation is in BCNF.
    """
    for pair in specific_FDs
        lhs = pair[1]
        rhs = pair[2]

        lhs_closure = attribute_closure(lhs, All_FDs)
        if attributes != lhs_closure
            if verbose
                println("LHS = ", lhs, " with closure ",lhs_closure," is NOT a superkey for the relation = ", attributes,"! Returning false.")
            end
            return false
        else
            if verbose
                println("LHS = ", lhs, " is a superkey for the relation, continuing search...")
            end
        end
    end
    if verbose
        println("All LHS in FDs are superkeys; Relation must be in BCNF form!")
    end
    return true
end

## BCNF Decomposition: Given a list of attributes and a set of FD's,
 # we calcualte the BCNF decomposition of R
function BCNF_decomp(attributes::Set, FDs::Set; verbose::Bool=false)
    for fd_pair in FDs
        fd_individual = Set([fd_pair])
        if(!is_BCNF(FDs, fd_individual, attributes, verbose=false))
            if verbose
                println("Violating FD: ", fd_individual)
            end

            X = fd_pair[1] # LHS of the offending FD
            Y = fd_pair[2] # RHS of the offending FD
            # println("X has type ", typeof(X))

            println("\tX: ", X)
            X_plus = attribute_closure(X, FDs)

            attributes_1 = X_plus
            attributes_2 = setdiff(attributes, setdiff(X_plus, X))


            FDs_1 = project(FDs, attributes_1)
            FDs_2 = project(FDs, attributes_2)

            if verbose
                println("Attributes 1: ", X_plus)
                println("Attributes 2: ", attributes_2)
            end

            # if length(attributes_1) == 0 && length(attributes_2) != 0
            #     return BCNF_decomp(attributes_2, FDs_2)
            # elseif length(attributes_2) == 0 && length(attributes_1) != 0
            #     return BCNF_decomp(attributes_1, FDs_1)
            # else
            #     return vcat(BCNF_decomp(attributes_1, FDs_1), BCNF_decomp(attributes_2, FDs_2))
            # end

            # Recursive step
            return vcat(BCNF_decomp(attributes_1, FDs_1), BCNF_decomp(attributes_2, FDs_2))

        end
    end
    return [attributes]
end
