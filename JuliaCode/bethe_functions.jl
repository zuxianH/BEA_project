using CSV, DataFrames,BifurcationKit,Plots,JLD2,Serialization,LinearAlgebra,Suppressor,ForwardDiff, Statistics

# Extract the last solution
function extract_last_solution(br)
    last_point = br.branch[end]
    get_last_solution = collect(values(last_point)[1:length(u0)])
    return get_last_solution
end


# Export the last solution to a CSV file
function export_last_solution_to_csv(br, filename="get_last_solution.csv")
    last_point = br.branch[end]
    get_last_solution = collect(values(last_point)[1:length(u0)])
    df_out = DataFrame(var = string.(vars[1:end-1]), b_final_value = get_last_solution)
    CSV.write(filename, df_out)
end

# Export the entire branch to a CSV file
function export_branch_to_csv(br, filename="all_branch.csv")
    branch_df = DataFrame([pt for pt in br.branch])
    for col in names(branch_df)
        if eltype(branch_df[!, col]) == Nothing
            branch_df[!, col] = Any[branch_df[!, col]...]  # convert to Any
        end
        replace!(branch_df[!, col], nothing => missing)
    end
    CSV.write(filename, branch_df)
end

# Plot the solution against the parameter values for a given variable or index
function plot_solution(br, var_or_index)
    p_vals = [pt.param for pt in br.branch]
    plt = plot(
        title="solution vs λ",
        xlabel="λ",
        ylabel="value",
        legend=:outerright
    )
    if isa(var_or_index, Symbol) || isa(var_or_index, Int)
        var_or_index = [var_or_index]
    end
    for v in var_or_index
        x_vals = isa(v, Symbol) ? [getfield(pt, v) for pt in br.branch] : [collect(values(pt))[v] for pt in br.branch]
        plot!(plt, p_vals, x_vals; seriestype=:scatter, label=string(v))
    end
    return plt
end


######################################################################
function load_scale_data_and_initialize(λ0::Float64, path::String)
    global vars, vars_init, expr_funcs, df, load_initial_data
    load_initial_data = CSV.read(path, DataFrame)
    # Extract the expressions and variable names
    original_exprs = load_initial_data.expression
    b_vars = load_initial_data.var
    vars = Symbol.(vcat(b_vars, "h"))
    initialvar_processed = replace.(string.(load_initial_data.Initialvar), r"\*10\^" => "e")
    vars_init = BigFloat.(initialvar_processed)
    
    # Scale variables in expressions
    scaled_expressions = copy(original_exprs)
    for (i, expr) in enumerate(scaled_expressions)
        modified_expr = expr
        for v in b_vars
            # Use word boundaries to ensure we're replacing complete variable names
            modified_expr = replace(modified_expr, Regex("\\b$v\\b") => "($(λ0)*$v)")
        end
        scaled_expressions[i] = modified_expr
    end
    df = scaled_expressions
    
    # Load the expressions from the CSV file with λ0 in scope
    expr_funcs = let λ0=λ0
        [eval(Expr(:->, Expr(:tuple, vars...), Meta.parse(expr)))
         for expr in df]
    end
end


function load_data_and_initialize(path::String)
    global vars, vars_init, expr_funcs,df
    # Load the CSV file
    load_initial_data = CSV.read(path, DataFrame)
    # Extract the expressions and variable names
    df = load_initial_data.expression
    vars = Symbol.(vcat(load_initial_data.var, "h"))
    #vars_init = BigFloat.(replace.(load_initial_data.Initialvar, r"`.*" => ""))
    initialvar_processed = replace.(string.(load_initial_data.Initialvar), r"\*10\^" => "e")
    vars_init = BigFloat.(initialvar_processed)
    # Load the expressions from the CSV file
    expr_funcs = [
        eval(Expr(:->, Expr(:tuple, vars...), Meta.parse(expr)))
        for expr in df
    ]
end


# Define the general evaluation function
function G(u, p)
    args = vcat(u, p)
    return [f(args...) for f in expr_funcs]  
end;



# Define a struct to hold continuation parameters
mutable struct ParameterOpts
    ds::Float64
    dsmax::Float64
    dsmin::Float64
    lambda0::Float64
    max_newton_iterations::Int64
    newton_tol::Float64
    a::Float64
    verbose::Bool
end


function make_opts(opts::ParameterOpts)
    return ContinuationPar(
        ds = opts.ds,
        dsmin = opts.dsmin, 
        dsmax = opts.dsmax,
        p_min = 0.,
        p_max = opts.lambda0,
        max_steps = 1e5,
        newton_options = NewtonPar(
            tol = opts.newton_tol,
            max_iterations = opts.max_newton_iterations,
            verbose = opts.verbose),
        detect_bifurcation = 0,
        detect_event = 0,
        a = opts.a,
        detect_loop = false
    )
end


function run_continuation_with_tol(
    prob::BifurcationProblem, 
    method, 
    opts::ParameterOpts=myOpts; 
    dp_tol=0.3, 
    max_tol=1e-4, 
    tol_multiplier=10.0)
    
    local_opts = deepcopy(opts)
    #local_opts.newton_tol = initial_tol  initial_tol=1e-12,
    
    while local_opts.newton_tol <= max_tol
        cont_opts = make_opts(local_opts)
        
        br = continuation(
            prob,
            method,
            cont_opts,
            normC = norminf,
            callback_newton = (state; kwargs...) -> cb(state; kwargs..., dp=dp_tol),
            verbosity = my_verbosity
        )
        # Check immediately if we've reached the target
        if br.sol[end].p == 0
            return br
        end
        
        # Log the current value and increase tolerance
        @info "Failed to reach target (p=$(br.sol[end].p)) with tol=$(local_opts.newton_tol), increasing tolerance"
        local_opts.newton_tol *= tol_multiplier
    end
    
    # If we get here, we've exceeded max_tol
    error("Failed to reach br.sol[end].p == 0 even at maximum tolerance $(max_tol)")
end





#=
function run_lazy(prob, dp_tol::Float64,myOpts)
    run = run_continuation_with_tol(
        prob,
        PALC(tangent = Bordered(),θ=0.5), 
        #MoorePenrose(method = BifurcationKit.iterative),
        myOpts,
        dp_tol=dp_tol,
        max_tol=1e-2)
    return run
end
=#

function run_continuation_with_tol(
    prob::BifurcationProblem, 
    method, 
    opts::ParameterOpts=myOpts; 
    dp_tol)
    
    br = continuation(
            prob,
            method,
            make_opts(opts),
            normC = norminf,
            callback_newton = (state; kwargs...) -> cb(state; kwargs..., dp=dp_tol),
            verbosity = my_verbosity
        )
    return br 
end

function run_lazy(prob, dp_tol::Float64,myOpts)
    run = run_continuation_with_tol(
        prob,
        PALC(tangent = Bordered(),θ=0.5), 
        #MoorePenrose(method = BifurcationKit.iterative),
        myOpts,
        dp_tol=dp_tol)
    return run
end

# function my_tol_x(indices)
#     if length(indices) == 0
#         return 0.01  # Default tolerance if no indices are provided
#     else
#         return my_dx_tol  # Adjust as needed for the specific indices
#     end
# end

# function cb(state; dp, kwargs...)
#     _x        = get(kwargs, :z0, nothing)
#     fromNewton = get(kwargs, :fromNewton, false)
#     if !fromNewton && _x !== nothing
#         dp_jump = abs(_x.p - state.p)
#         dx_vals = abs.(_x.u[indices] .- state.x[indices])  # Compute differences for all indices
#         tol_vals = my_tol_x(indices)                      # Get tolerances for all indices
#         if any(dx_vals .> tol_vals) || dp_jump > dp       # Check if any dx exceeds tolerance or dp_jump is too large
#             return false
#         end
#     end
#     return true
# end


function cb(state; dp, kwargs...)
    _x = get(kwargs, :z0, nothing)  # Previous solution
    fromNewton = get(kwargs, :fromNewton, false)
    
    if !fromNewton && _x !== nothing
        dp_jump = abs(_x.p - state.p)  # Change in parameter
        dx_vals = abs.(_x.u .- state.x)  # Change in solution
        
        # Define tolerances dynamically
        tol_vals = [0.01 * max(1, abs(x)) for x in state.x]
        
        # Check if any dx exceeds tolerance or dp_jump is too large
        if any(dx_vals .> tol_vals) || dp_jump > dp
            return false
        end
    end
    
    return true
end


using GLMakie

function dymamic_plot()
    fig = Figure()
    ax1 = Axis(fig[1, 1])
    ax2 = Axis(fig[2, 1])

    sl_sol = Slider(fig[3, 1], range = 1:length(final_result.sol[1].x), startvalue = 1, update_while_dragging=true)
    label = Label(fig[3, 2], lift(x -> "Component: $x", sl_sol.value))

    x = [get_solp(final_result, i) for i in 1:length(final_result)]

    y_lift = lift(sl_sol.value) do sol
        y = [get_solx(final_result, i)[sol] for i in 1:length(final_result)]
        ymin, ymax = minimum(y), maximum(y)
        margin = 0.1 * (ymax - ymin + eps())  # add 10% margin
        GLMakie.ylims!(ax1, ymin - margin, ymax + margin)
        y
    end

    diff_y_lift = lift(y_lift) do y
        dy = abs.(diff(y))
        ymin, ymax = minimum(dy), maximum(dy)
        margin = 0.1 * (ymax - ymin + eps())
        GLMakie.ylims!(ax2, ymin - margin, ymax + margin)
        dy
    end

    GLMakie.scatter!(ax1, x, y_lift)
    GLMakie.lines!(ax2, diff_y_lift)

    fig
end 