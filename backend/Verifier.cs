
/* Copyright 2022 Xingyu Xie

This file is part of CMinor.

CMinor is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

CMinor is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with CMinor. If not, see <https://www.gnu.org/licenses/>. */

/*
    TODO: 这是你唯一允许编辑的文件，你可以对此文件作任意的修改，只要整个项目可以正常地跑起来。
*/

using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics;
using CommandLine;

namespace cminor
{
    /// <summary> 一个验证器，接受一个中间表示，判断其是否有效。 </summary>
    class Verifier
    {
        SMTSolver solver = new SMTSolver();
        TextWriter writer;
        HashSet<int> visitedLoopHeads = new();

        public Verifier(TextWriter writer)
        {
            this.writer = writer;
        }

        static private Expression ConditionToExpression(List<Expression> conditions)
        {
            Expression exp = new BoolConstantExpression(true);
            for (int i = 0; i < conditions.Count; i++)
                exp = new AndExpression(exp, conditions[i]);
            return exp;
        }

        static private Expression FunEntryRequire(FunctionCallStatement fcs)
        {
            Function fun = fcs.rhs.function;
            Expression assertExpr = ConditionToExpression(fun.preconditionBlock.conditions);

            Debug.Assert(fcs.rhs.argumentVariables.Count == fun.parameters.Count, "FunctionCallStatement's argumentVariables count must match the function's parameters count.");

            for (int i = 0; i < fun.parameters.Count; i++)
            {
                VariableExpression varExpr = new(fcs.rhs.argumentVariables[i]);
                assertExpr = assertExpr.Substitute(fun.parameters[i], varExpr);
            }

            return assertExpr;
        }

        static private AssumeStatement FunReturnEnsure(FunctionCallStatement fcs)
        {
            Function fun = fcs.rhs.function;
            Expression assumeExpr = ConditionToExpression(fun.postconditionBlock.conditions);

            Debug.Assert(fcs.rhs.argumentVariables.Count == fun.parameters.Count, "FunctionCallStatement's argumentVariables count must match the function's parameters count.");

            for (int i = 0; i < fun.parameters.Count; i++)
            {
                VariableExpression varExpr = new(fcs.rhs.argumentVariables[i]);
                assumeExpr = assumeExpr.Substitute(fun.parameters[i], varExpr);
            }

            for (int i = 0; i < fun.rvs.Count; i++)
            {
                VariableExpression varExpr = new(fcs.lhs[i]);
                assumeExpr = assumeExpr.Substitute(fun.rvs[i], varExpr);
            }

            AssumeStatement assumeStmt = new() { condition = assumeExpr };
            return assumeStmt;
        }

        static private Expression LexLess(List<Expression> a, List<Expression> b)
        {
            // lexicographic less than based on well-founded relation
            Debug.Assert(a.Count == b.Count, "LexLess: a and b must have the same length.");
            var zero = new IntConstantExpression(0);
            Expression res = new AndExpression(new LTExpression(a[0], b[0]), new GEExpression(b[0], zero));
            for (int i = 1; i < a.Count; i++)
            {
                Expression expr = new AndExpression(new LTExpression(a[i], b[i]), new GEExpression(b[i], zero));
                for (int j = 0; j < i; j++)
                {
                    expr = new AndExpression(expr, new EQExpression(a[j], b[j]));
                }
                res = new OrExpression(res, expr);
            }
            return res;
        }

        static private Expression PredicateTransform(Expression p, List<Statement> statements)
        {
            Expression wlp = p;
            foreach (var stmt in statements.AsEnumerable().Reverse())
            {
                if (stmt is AssumeStatement assumeStmt)
                {
                    wlp = new ImplicationExpression(assumeStmt.condition, wlp);
                }
                else if (stmt is VariableAssignStatement vas)
                {
                    wlp = wlp.Substitute(vas.variable, vas.rhs);
                }
                else if (stmt is SubscriptAssignStatement sas)
                {
                    VariableExpression array = new(sas.array);
                    VariableExpression arrayLength = new(sas.array.length);
                    ArrayUpdateExpression arrayUpdate = new(array, sas.subscript, sas.rhs, arrayLength);
                    wlp = wlp.Substitute(sas.array, arrayUpdate);
                }
                else throw new Exception("Weird statement type in basic path: " + stmt.GetType());
                // wlp.Print(writer);
                // writer.WriteLine();
            }
            return wlp;
        }

        private int CheckBasicPath(BasicPath bp)
        {
            writer.WriteLine("============================");
            writer.WriteLine("Checking basic path: ");
            writer.WriteLine("Head conditions:");
            bp.headConditions.ForEach(c => c.Print(writer));
            writer.WriteLine("\nstatements:");
            foreach (var stmt in bp.statements)
            {
                stmt.Print(writer);
            }
            writer.WriteLine("Tail conditions:");
            bp.tailConditions.ForEach(c => c.Print(writer));
            writer.WriteLine("\n");

            // Partial Correctness
            Expression wlp = ConditionToExpression(bp.tailConditions);
            wlp = PredicateTransform(wlp, bp.statements);
            Expression precond = ConditionToExpression(bp.headConditions);
            var res = solver.CheckValid(new ImplicationExpression(precond, wlp));
            if (res is not null) return -1;

            // Total Correctness (termination)
            List<Expression> headRank = bp.headRankingFunctions;
            List<Expression> tailRank = bp.tailRankingFunctions;
            if (headRank.Count == 0) return 1;
            if (tailRank.Count == 0)
            {
                Expression nonNeg = new BoolConstantExpression(true);
                foreach (var hr in headRank)
                {
                    nonNeg = new AndExpression(nonNeg, new GEExpression(hr, new IntConstantExpression(0)));
                }
                res = solver.CheckValid(new ImplicationExpression(precond, nonNeg));
                if (res is not null) return -1;
                return 1;
            }

            Dictionary<LocalVariable, Expression> varSubstitutions = new();
            for (int i = 0; i < headRank.Count; i++)
            {
                Expression currentHr = headRank[i];
                foreach (var v in currentHr.GetFreeVariables())
                {
                    var newVar = new LocalVariable { type = v.type, name = v.name + "_head" };
                    varSubstitutions[newVar] = new VariableExpression(v);
                    currentHr = currentHr.Substitute(v, new VariableExpression(newVar));
                }
                headRank[i] = currentHr;
            }

            Expression dec = LexLess(tailRank, headRank);
            dec = PredicateTransform(dec, bp.statements);

            foreach (var v in varSubstitutions.Keys)
                dec = dec.Substitute(v, varSubstitutions[v]);
            precond.Print(writer);
            writer.WriteLine();
            dec.Print(writer);
            writer.WriteLine();
            ImplicationExpression impl = new(precond, dec);
            res = solver.CheckValid(impl);
            if (res is not null) return -1;
            return 1;
        }

        static private BasicPath Deepcopy(BasicPath bp)
        {
            return new()
            {
                headConditions = new List<Expression>(bp.headConditions),
                headRankingFunctions = new List<Expression>(bp.headRankingFunctions),
                tailConditions = new List<Expression>(bp.tailConditions),
                tailRankingFunctions = new List<Expression>(bp.tailRankingFunctions),
                statements = new List<Statement>(bp.statements)
            };
        }

        static private Expression Deepcopy(Expression exp)
        {
            // Cervol: There's no clone method for the Expression abstract class, so 
            // I have to use the Substitute method to make a deep copy indirectly.
            // This is a hack, not a good approach.
            var dummyVar = new LocalVariable { type = exp.type, name = "dummy" };
            return exp.Substitute(dummyVar, new VariableExpression(dummyVar));
        }

        private int DfsCFG(Block u, BasicPath bp)
        {
            u.Print(writer); writer.WriteLine();
            switch (u)
            {
                case PreconditionBlock:
                    PreconditionBlock pre = (PreconditionBlock)u;
                    bp.headConditions = pre.conditions;
                    bp.headRankingFunctions = pre.rankingFunctions;
                    foreach (Block v in pre.successors)
                        if (DfsCFG(v, Deepcopy(bp)) < 0) return -1;
                    break;

                case PostconditionBlock:
                    PostconditionBlock post = (PostconditionBlock)u;
                    bp.tailConditions = post.conditions;
                    return CheckBasicPath(bp);

                case LoopHeadBlock:
                    LoopHeadBlock loopHead = (LoopHeadBlock)u;

                    if (!visitedLoopHeads.Contains(loopHead.number))
                    {
                        visitedLoopHeads.Add(loopHead.number);
                        BasicPath bp_ = new()
                        {
                            headConditions = loopHead.invariants,
                            headRankingFunctions = loopHead.rankingFunctions
                        };
                        foreach (Statement stmt in loopHead.statements)
                            bp_.statements.Add(stmt);
                        foreach (Block v in loopHead.successors)
                            if (DfsCFG(v, Deepcopy(bp_)) < 0) return -1;
                    }

                    bp.tailConditions = loopHead.invariants;
                    bp.tailRankingFunctions = loopHead.rankingFunctions;
                    return CheckBasicPath(bp);

                case BasicBlock:
                    BasicBlock basic = (BasicBlock)u;
                    foreach (Statement s in basic.statements)
                    {
                        if (s is AssertStatement assertStmt)
                        {
                            BasicPath bp_ = Deepcopy(bp);
                            bp_.tailConditions = new List<Expression> { assertStmt.pred };
                            if (CheckBasicPath(bp_) < 0) return -1;

                            AssumeStatement assumeStmt = new() { condition = assertStmt.pred };
                            bp.statements.Add(assumeStmt);
                        }
                        else if (s is AssumeStatement or AssignStatement)
                        {
                            bp.statements.Add(s);
                        }
                        else if (s is FunctionCallStatement fcs)
                        {
                            var fun = fcs.rhs.function;
                            Debug.Assert(fun.parameters.Count == fcs.rhs.argumentVariables.Count,
                                "FunctionCallStatement's argumentVariables count must match the function's parameters count.");
                            var rankFuns = fun.preconditionBlock.rankingFunctions;
                            BasicPath bp_ = Deepcopy(bp);
                            bp_.tailConditions = new List<Expression> { FunEntryRequire(fcs) };
                            bp_.tailRankingFunctions = new List<Expression> { };
                            for (int i = 0; i < rankFuns.Count; i++)
                            {
                                var rf = Deepcopy(rankFuns[i]);
                                for (int j = 0; j < fun.parameters.Count; j++)
                                {
                                    VariableExpression argVar = new(fcs.rhs.argumentVariables[j]);
                                    rf = rf.Substitute(fun.parameters[j], argVar);
                                }
                                bp_.tailRankingFunctions.Add(rf);
                            }
                            if (CheckBasicPath(bp_) < 0) return -1;

                            bp.statements.Add(FunReturnEnsure(fcs));
                        }
                    }
                    foreach (Block v in basic.successors)
                        if (DfsCFG(v, Deepcopy(bp)) < 0) return -1;
                    break;

                default:
                    return 0;
            }
            return 1;
        }

        private int ApplyFun(Function fun)
        {
            return DfsCFG(fun.preconditionBlock, new BasicPath());
        }

        /// <summary> 应用此验证器 </summary>
        /// <param name="cfg"> 待验证的控制流图 </param>
        /// <returns> 验证结果 </returns>
        /// <list type="bullet">
        ///     <item> “&gt; 0” 表示所有的 specification 都成立 </item>
        ///     <item> “&lt; 0” 表示有一个 specification 不成立 </item>
        ///     <item> “= 0” 表示 unknown </item>
        /// </list>
        public int Apply(IRMain cfg)
        {
            foreach (Predicate predicate in cfg.predicates)
            {
                solver.definePredicate(predicate);
            }
            int result = 1;
            foreach (Function fun in cfg.functions)
            {
                int res = ApplyFun(fun);
                if (res < 0) return res;
                else if (res == 0) 
                {
                    result = 0;
                }
            }
            return result;
        }
    }
}

