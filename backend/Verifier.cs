
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

        private Expression ConditionToExpression(List<Expression> conditions)
        {
            if(conditions.Count == 0) return new BoolConstantExpression(true);
            Expression exp = conditions[0];
            for (int i = 1; i < conditions.Count; i++)
            {
                Expression expr = conditions[i];
                exp = new AndExpression(exp, expr);
            }
            return exp;
        }

        private Expression FunEntryRequire(FunctionCallStatement fcs)
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

        private AssumeStatement FunReturnEnsure(FunctionCallStatement fcs)
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

        private int CheckBasicPath(BasicPath bp)
        {
            // writer.WriteLine("Checking basic path: ");
            // writer.WriteLine("Head conditions:");
            // bp.headConditions.ForEach(c => c.Print(writer));
            // writer.WriteLine("\nstatements:");
            // foreach (var stmt in bp.statements)
            // {
            //     stmt.Print(writer);
            // }
            // writer.WriteLine("Tail conditions:");
            // bp.tailConditions.ForEach(c => c.Print(writer));
            // writer.WriteLine("\n");
            Expression wlp = ConditionToExpression(bp.tailConditions);
            foreach (var stmt in bp.statements.AsEnumerable().Reverse())
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
            Expression precond = ConditionToExpression(bp.headConditions);
            var res = solver.CheckValid(new ImplicationExpression(precond, wlp));
            if (res is null) return 1;
            return -1;
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

        private int DfsCFG(Block u, BasicPath bp)
        {
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
                            // TODO: bp_.tailRankingFunctions = new List<Expression>();
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
                            BasicPath bp_ = Deepcopy(bp);
                            bp_.tailConditions = new List<Expression> { FunEntryRequire(fcs) };
                            // TODO: bp_.tailRankingFunctions = new List<Expression>();
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

