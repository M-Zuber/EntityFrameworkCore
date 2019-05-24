// Copyright (c) .NET Foundation. All rights reserved.
// Licensed under the Apache License, Version 2.0. See License.txt in the project root for license information.

using System;
using System.Collections.Generic;
using System.ComponentModel.Design;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Linq.Expressions;
using System.Reflection;
using JetBrains.Annotations;
using Microsoft.EntityFrameworkCore.Diagnostics;
using Microsoft.EntityFrameworkCore.Extensions.Internal;
using Microsoft.EntityFrameworkCore.Infrastructure;
using Microsoft.EntityFrameworkCore.Internal;
using Microsoft.EntityFrameworkCore.Metadata;
using Microsoft.EntityFrameworkCore.Metadata.Internal;
using Microsoft.EntityFrameworkCore.Utilities;
using Remotion.Linq.Clauses.Expressions;

namespace Microsoft.EntityFrameworkCore.Query.Pipeline
{
    /// <summary>
    /// Rewrites comparisons of entities (as opposed to comparisons of their properties) into comparison of their keys.
    /// </summary>
    /// <remarks>
    /// For example, an expression such as cs.Where(c => c == something) would be rewritten to cs.Where(c => c.Id == something.Id).
    /// </remarks>
    [SuppressMessage("ReSharper", "AssignNullToNotNullAttribute")]  // TODO: Check
    public class EntityEqualityRewritingExpressionVisitor2 : ExpressionVisitor
    {
        private readonly IModel _model;

        [CanBeNull]
        private IEntityType _mainEntityType;

        // TODO: Use arrays or something, we're not going to have a large number here?
        [NotNull]
        private Dictionary<ParameterExpression, IEntityType> _parameterBindings;

        private Stack<(IEntityType MainEntityType, Dictionary<ParameterExpression, IEntityType> ParameterBindings)> _stack;

        public EntityEqualityRewritingExpressionVisitor2([NotNull] IModel model)
        {
            _model = model;
            _mainEntityType = null;
            _parameterBindings = new Dictionary<ParameterExpression, IEntityType>();
            _stack = new Stack<(IEntityType MainEntityType, Dictionary<ParameterExpression, IEntityType> ParameterBindings)>();
        }

        #region Traversal expressions

        protected override Expression VisitConstant(ConstantExpression constantExpression)
        {
            if (constantExpression.IsEntityQueryable())
            {
                _mainEntityType = _model.FindEntityType(((IQueryable)constantExpression.Value).ElementType);
            }

            return constantExpression;
        }

        protected override Expression VisitMember(MemberExpression memberExpression)
        {
            var newExpression = (MemberExpression)base.VisitMember(memberExpression);

            _mainEntityType = _mainEntityType?.FindNavigation(newExpression.Member.Name) is INavigation navigation
                ? navigation.GetTargetType()
                : null;   // TODO: PostgreSQL composite support would go here

            return newExpression;
        }

        protected override Expression VisitParameter(ParameterExpression parameterExpression)
        {
            _mainEntityType = _parameterBindings.TryGetValue(parameterExpression, out var parameterEntityType)
                ? parameterEntityType
                : null;
            return parameterExpression;
        }

        protected override Expression VisitMethodCall(MethodCallExpression methodCallExpression)
        {
            // Navigation via EF.Property() or via an indexer property
            if (methodCallExpression.TryGetEFPropertyArguments(out _, out var propertyName)
                || methodCallExpression.TryGetEFIndexerArguments(out _, out propertyName))
            {
                _mainEntityType = _mainEntityType.FindNavigation(propertyName) is INavigation navigation
                    ? navigation.GetTargetType()
                    : null;
                return base.VisitMethodCall(methodCallExpression);
            }

            var args = methodCallExpression.Arguments;

            if (methodCallExpression.Method.DeclaringType == typeof(Queryable)
                || methodCallExpression.Method.DeclaringType == typeof(EntityQueryableExtensions))
            {
                switch (methodCallExpression.Method.Name)
                {
                    // TODO: We can actually infer if the method flows the entity type by checking whether its return type is the same
                    // as its first parameter type.
                    case nameof(Queryable.Concat):
                    case nameof(Queryable.DefaultIfEmpty):
                    case nameof(Queryable.Distinct):
                    case nameof(Queryable.ElementAtOrDefault):
                    case nameof(Queryable.Except):
                    case nameof(Queryable.FirstOrDefault):
                    case nameof(Queryable.Intersect):
                    case nameof(Queryable.LastOrDefault):
                    case nameof(Queryable.OrderBy):
                    case nameof(Queryable.Reverse):
                    case nameof(Queryable.SingleOrDefault):
                    case nameof(Queryable.Skip):
                    case nameof(Queryable.SkipWhile):
                    case nameof(Queryable.Take):
                    case nameof(Queryable.TakeWhile):
                    case nameof(Queryable.ThenBy):
                    case nameof(Queryable.Union):
                    case nameof(Queryable.Where):
                        // Methods which flow the entity type through, some requiring lambda rewriting
                        return RewriteSimpleMethodIfNeeded(methodCallExpression);

                    case nameof(Queryable.All):
                    case nameof(Queryable.Any):
                    case nameof(Queryable.Average):
                    case nameof(Queryable.Contains):
                    case nameof(Queryable.Count):
                    case nameof(Queryable.LongCount):
                    case nameof(Queryable.Max):
                    case nameof(Queryable.Min):
                    case nameof(Queryable.Sum):
                    {
                        // Reducing methods; some have lambdas to rewrite, none flow the entity type.
                        var newMethodCallExpression = RewriteSimpleMethodIfNeeded(methodCallExpression);
                        _mainEntityType = null;
                        return newMethodCallExpression;
                    }

                    case nameof(Queryable.Select) when args.Count == 2:
                    {
                        // TODO: This does not handle anonymous types yet
                        var newSource = Visit(args[0]);
                        var quote = (UnaryExpression)methodCallExpression.Arguments[1];
                        var lambda = (LambdaExpression)quote.Operand;
                        PushStackFrame(lambda.Parameters[0], _mainEntityType);
                        var newQuote = Visit(quote);
                        PopStackFrame(true);
                        return newSource != args[0] || newQuote != quote
                               ? Expression.Call(null, methodCallExpression.Method, newSource, newQuote)
                               : methodCallExpression;
                    }

                    case nameof(Queryable.Cast):
                    case nameof(Queryable.OfType):
                        // TODO: Do these preserve the entity type as far as keys are concerned (are keys shared in the entity hierarchy?)
                    case nameof(Queryable.GroupBy):
                    case nameof(Queryable.GroupJoin):
                    case nameof(Queryable.Join):
                    case nameof(EntityQueryableExtensions.LeftJoin):
                    case nameof(Queryable.SelectMany):
                        throw new NotImplementedException();
                }
            }

            // TODO: We need to identify FromSql{Raw,Interpolated} but those are in relational. For now we match by name, should
            // subclass visitor instead and move to the extension point below.
            if (methodCallExpression.Method.DeclaringType.Name == "RelationalEntityQueryableExtensions"
                && methodCallExpression.Method.Name == "FromSqlOnQueryable")
            {
                // FromSql{Raw,Interpolated} simply flow the entity type; no action needed.
                return methodCallExpression;
            }

            // If we're here, the this is an unknown method call.
            // TODO: Need an extension point that can be overridden by subclassing visitors to recognize additional methods and flow through the entity type.
            _mainEntityType = null;
            return methodCallExpression;
        }

        // If the method accepts a single lambda with a single parameter, assumes the parameter corresponds to the first argument
        // and visits the lambda, performing the necessary rewriting.
        private Expression RewriteSimpleMethodIfNeeded(MethodCallExpression methodCallExpression)
        {
            var foundLambda = false;
            Expression[] newArguments = null;
            for (var i = 0; i < methodCallExpression.Arguments.Count; i++)
            {
                var arg = methodCallExpression.Arguments[i];
                Expression newArg;
                switch (arg)
                {
                    case UnaryExpression quote when quote.NodeType == ExpressionType.Quote:
                    {
                        var lambda = (LambdaExpression)quote.Operand;
                        if (foundLambda || lambda.Parameters.Count != 1)
                        {
                            throw new NotSupportedException("Cannot rewrite method with more than one lambda or lambda parameter: " +
                                                            methodCallExpression.Method.Name);
                        }

                        PushStackFrame(lambda.Parameters[0], _mainEntityType);
                        newArg = Visit(quote);
                        PopStackFrame();

                        foundLambda = true;
                        break;
                    }

                    default:
                        newArg = Visit(arg);
                        break;
                }

                // Write the visited argument into a new arguments array, but only if any argument has already been modified
                if (newArg != arg)
                {
                    if (newArguments == null)
                    {
                        newArguments = new Expression[methodCallExpression.Arguments.Count];
                        methodCallExpression.Arguments.CopyTo(newArguments, 0);
                    }
                }

                if (newArguments != null)
                {
                    newArguments[i] = newArg;
                }
            }

            return methodCallExpression.Update(
                Visit(methodCallExpression.Object),
                (IEnumerable<Expression>)newArguments ?? methodCallExpression.Arguments);
        }

        private void PushStackFrame(ParameterExpression newParameterExpression, IEntityType newEntityType)
        {
            _stack.Push((_mainEntityType, _parameterBindings));
            _mainEntityType = null;
            _parameterBindings = new Dictionary<ParameterExpression, IEntityType>(_parameterBindings)
            {
                { newParameterExpression, newEntityType }
            };
        }

        private void PopStackFrame(bool preserveMainEntityType = false)
        {
            var frame = _stack.Pop();
            _parameterBindings = frame.ParameterBindings;
            if (!preserveMainEntityType)
            {
                _mainEntityType = frame.MainEntityType;
            }
        }

        #endregion Traversal expressions

        #region Equality rewriting

        protected override Expression VisitBinary(BinaryExpression binaryExpression)
        {
            Check.NotNull(binaryExpression, nameof(binaryExpression));

            if (binaryExpression.NodeType != ExpressionType.Equal && binaryExpression.NodeType != ExpressionType.NotEqual)
            {
                // TODO: This is a safety measure for now - not sure if any other binary expressions can occur with entity types directly
                // as their operands. But just in case we don't flow.
                _mainEntityType = null;

                return base.VisitBinary(binaryExpression);
            }

            // Visit children and get their respective entity types
            _mainEntityType = null;
            var newLeft = Visit(binaryExpression.Left);
            var leftEntityType = _mainEntityType;
            var isLeftNullConstant = newLeft.IsNullConstantExpression();

            _mainEntityType = null;
            var newRight = Visit(binaryExpression.Right);
            var rightEntityType = _mainEntityType;
            var isRightNullConstant = newRight.IsNullConstantExpression();

            _mainEntityType = null;

            // Handle null constants
            if (isLeftNullConstant)
            {
                if (isRightNullConstant)
                {
                    return binaryExpression.NodeType == ExpressionType.Equal
                        ? Expression.Constant(true)
                        : Expression.Constant(false);
                }

                return RewriteNullEquality(binaryExpression.NodeType, newRight, rightEntityType);
            }

            if (isRightNullConstant)
            {
                return RewriteNullEquality(binaryExpression.NodeType, newLeft, leftEntityType);
            }

            // No null constants, check the entity types
            throw new NotImplementedException();

#if NOT_YET_IMPLEMENTED
            if (leftEntityType == null)
            {
                return rightEntityType == null
                         // No entities are involved, no rewriting necessary.
                       ? binaryExpression.Update(newLeft, binaryExpression.Conversion, newRight)
                       : RewriteEntityEquality();
            }

            if (rightEntityType == null)
            {
                return RewriteEntityEquality();
            }

            // Both sides are entities,

            // TODO: Confirm that inheritance logic here is correct
            return leftEntityType.IsSameHierarchy(rightEntityType)
                ? RewriteEntityEquality()
                : Expression.Constant(false);
#endif
        }

        private Expression RewriteNullEquality(ExpressionType nodeType, Expression nonNullExpression, IEntityType entityType)
        {
            var keyProperties = entityType.FindPrimaryKey().Properties;
            var nullCount = keyProperties.Count;

            Expression keyAccessExpression;

            // Skipping composite key with subquery since it requires to copy subquery
            // which would cause same subquery to be visited twice
            if (nullCount > 1 && nonNullExpression.RemoveConvert() is SubQueryExpression)
            {
                return null;
            }

            keyAccessExpression = CreateKeyAccessExpression(
                nonNullExpression,
                keyProperties,
                nullComparison: true);

            return Expression.MakeBinary(nodeType, keyAccessExpression, Expression.Constant(null));

        }

        private static Expression CreateKeyAccessExpression(
            Expression target,
            IReadOnlyList<IProperty> properties,
            bool nullComparison)
        {
            // If comparing with null then we need only first PK property
            return properties.Count == 1 || nullComparison
                ? target.CreateEFPropertyExpression(properties[0]) // TODO: Why via EF.Property()?
                : target.CreateKeyAccessExpression(properties);
        }

        #endregion Equality rewriting
    }
}
