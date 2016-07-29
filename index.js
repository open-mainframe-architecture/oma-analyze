"use strict";

const babylon = require('babylon');
const constants = require('oma-constants');
const traverse = require('babel-traverse').default;
const util = require('oma-util');

const AST = require('babel-types');

module.exports = archivePath => util.unzip(archivePath)
  .then(archive => {
    // collect class scripts of modules
    const readingClasses = [];
    const modules = archive.modules = {};
    for (const entry in archive.entries) {
      const moduleName = entry.substring(0, entry.indexOf('/'));
      if (moduleName.indexOf('.') > 0) {
        const classHome = `${moduleName}/${constants.module.classScripts.home}`;
        if (util.startsWith(entry, classHome)) {
          const classes = modules[moduleName] || (modules[moduleName] = {});
          const classPath = entry.substring(classHome.length + 1, entry.length - 3);
          const className = classPath.replace(util.vseps, '.');
          readingClasses.push(readClassScript(archive, entry, classes, className));
        }
      }
    }
    // when all class scripts have been read, forget about the archive and other assets
    return Promise.all(readingClasses).then(() => modules)
  })
  .then(modules => {
    // use synchronous calls to analyze class scripts
    const analysis_ = {};
    for (const moduleName in modules) {
      const classes = modules[moduleName];
      if (util.hasEnumerables(classes)) {
        const moduleAnalysis_ = {};
        for (const className in classes) {
          const scriptSource = classes[className];
          moduleAnalysis_[className] = analyzeClass(moduleName, className, scriptSource);
        }
        analysis_[moduleName] = { _: moduleAnalysis_ };
      }
    }
    return { _: analysis_ };
  })
  ;

function readClassScript(archive, entry, classes, className) {
  return util.unzipText(archive.file, archive.entries[entry])
    .then(scriptSource => { classes[className] = scriptSource; })
    ;
}

function visitedClass(visitor) {
  // module and class name identify particular class script
  return `~${visitor.moduleName}/${visitor.className}`;
}

function scriptSides(functionParams) {
  const names = {};
  for (let i = 0; i < 2; ++i) {
    const param = functionParams[i];
    if (param && param.type === 'Identifier') {
      // first parameter is instance side, second is class side
      names[param.name] = i ? 'class' : 'instance';
    }
  }
  return names;
}

function offset(keyword, member) {
  return { inside: keyword.literal.loc.start, from: member.loc.start, to: member.loc.end };
}

function aspect(analysis, name) {
  return analysis[name] || (analysis[name] = { _: {} });
}

var ClassVisitor = {
  Program: function(astPath) {
    if (astPath.node.body.length > 1) {
      throw new Error(`Too many statements: ${visitedClass(this)}`);
    }
  },
  'FunctionDeclaration|FunctionExpression': function(astPath) {
    if (!this.matchedScript) {
      // matched function (I, We) { }
      this.analysis.super = 'super';
      this.analysis.from = astPath.node.loc.start;
      this.scriptArguments = scriptSides(astPath.node.params);
      this.matchedScript = true;
    }
  },
  CallExpression: {
    enter: function(astPath) {
      const node = astPath.node, callee = node.callee, args = node.arguments;
      if (!this.matchedScript) {
        // match 'SuperExpression'.subclass(function(I, We) { })
        const script = args[args.length - 1];
        if (!AST.isMemberExpression(callee) || !AST.isStringLiteral(callee.object)
          || callee.computed || callee.property.name !== 'subclass' || !args.length
          || !AST.isFunctionExpression(script) && !AST.isArrowFunctionExpression(script)) {
          throw new Error(`Bad script: ${visitedClass(this)}`);
        }
        this.analysis.super = callee.object.value;
        this.analysis.from = script.loc.start;
        this.scriptArguments = scriptSides(script.params);
        this.matchedScript = true;
      } else if (!this.matchedKeyword &&
        AST.isMemberExpression(callee) && AST.isIdentifier(callee.object)
        && !callee.computed && (callee.object.name in this.scriptArguments)
        && args.length === 1 && AST.isObjectExpression(args[0])) {
        // matched I.keyword({ }) or We.keyword({ })
        this.matchedKeyword = {
          callSite: node,
          literal: args[0],
          side: this.scriptArguments[callee.object.name],
          keyword: callee.property.name
        };
      }
    },
    exit: function(astPath) {
      const matchedKeyword = this.matchedKeyword;
      if (matchedKeyword && matchedKeyword.callSite === astPath.node) {
        // start to look for next keyword
        this.matchedKeyword = false;
      }
    }
  },
  ObjectMember: function(astPath) {
    const matched = this.matchedKeyword, node = astPath.node;
    if (matched && matched.literal === astPath.parent && !node.computed) {
      const key = node.key.name, analysis = this.analysis, value = node.value;
      const keyword = matched.keyword, memberAnalysis = offset(matched, node);
      switch (keyword) {
        case 'nest':
          // traverse nested class with nested visitor
          const nestedClasses = aspect(analysis, 'nested');
          const nestedAnalysis = nestedClasses._[key] = memberAnalysis;
          astPath.traverse(ClassVisitor, {
            className: `${this.className}._.${key}`,
            moduleName: this.moduleName,
            analysis: nestedAnalysis
          });
          break;
        case 'am':
          // boolean flags
          if (!AST.isBooleanLiteral(value)) {
            throw new Error(`Bad flag: ${key} in ${visitedClass(this)}`);
          }
          memberAnalysis.value = value.value;
          aspect(analysis, 'flags')._[key] = memberAnalysis;
          break;
        case 'have':
          // instance/class variables
          aspect(analysis, `${matched.side}Variables`)._[key] = memberAnalysis;
          break;
        case 'access':
          // instance/class accessors
          aspect(analysis, `${matched.side}Accessors`)._[key] = memberAnalysis;
          break;
        case 'know':
          if (AST.isNullLiteral(value)) {
            // instance/class constants
            aspect(analysis, `${matched.side}Constants`)._[key] = memberAnalysis;
          } else {
            // instance/class methods
            aspect(analysis, `${matched.side}Methods`)._[key] = memberAnalysis;
          }
          break;
        case 'refine':
          // refinements of instance/class methods
          aspect(analysis, `${matched.side}Refinements`)._[key] = memberAnalysis;
          break;
        case 'setup':
        case 'share':
          // package constants and subroutines
          aspect(analysis, 'package')._[key] = memberAnalysis;
          break;
        default:
          // collect unknown aspect of instance or class side
          aspect(aspect(analysis, matched.side)._, keyword)._[key] = memberAnalysis;
      }
    }
  }
};

function analyzeClass(moduleName, className, scriptSource) {
  const ast = babylon.parse(scriptSource), classAnalysis = {}, state = {
    moduleName: moduleName,
    className: className,
    analysis: classAnalysis
  };
  traverse(ast, ClassVisitor, null, state);
  const remarks = ast.comments
    // remark starts with at-sign, otherwise it's a regular comment
    .filter(comment => comment.value.length > 1 && comment.value.charAt(0) === '@')
    .map(remark => ({ value: remark.value, from: remark.loc.start }));
  if (remarks.length) {
    collectRemarks(remarks, classAnalysis);
  }
  return classAnalysis;
}

function collectRemarks(remarks, classAnalysis, nested) {
  if (!nested) {
    const n = remarks.length, classRemarks = [];
    for (let i = 0; i < n && comparePosition(remarks[i].from, classAnalysis.from) < 0; ++i) {
      classRemarks.push(remarks[i]);
    }
    if (classRemarks.length) {
      classAnalysis.remarks = classRemarks;
    }
  }
  for (const aspectName in classAnalysis) {
    switch (aspectName) {
      case 'instance': case 'class':
        const nestedSide = classAnalysis[aspectName]._;
        for (const keywordName in nestedSide) {
          placeRemarks(remarks, nestedSide[keywordName]._);
        }
        break;
      case 'nested':
        const nestedClasses = classAnalysis.nested._;
        for (const nestedName in nestedClasses) {
          collectRemarks(remarks, nestedClasses[nestedName], true);
        }
        placeRemarks(remarks, nestedClasses);
        break;
      default:
        if (classAnalysis[aspectName]._) {
          placeRemarks(remarks, classAnalysis[aspectName]._);
        }
    }
  }
}

function placeRemarks(sortedRemarks, analysisEntries) {
  const sortedNames = Object.keys(analysisEntries).sort((leftKey, rightKey) =>
    comparePosition(analysisEntries[leftKey].from, analysisEntries[rightKey].from)
  );
  // either run out of remarks or run out of entries
  const n = sortedRemarks.length, m = sortedNames.length;
  for (let i = 0, j = 0; i < n && j < m;) {
    const remark = sortedRemarks[i], entry = analysisEntries[sortedNames[j]];
    if (comparePosition(remark.from, entry.inside) < 0) {
      // goto next remark if it does not start before the literal where the first entry is found
      ++i;
    } else if (comparePosition(remark.from, entry.from) < 0) {
      // add remark if it starts before the first entry
      const entryRemarks = entry.remarks || (entry.remarks = []);
      entryRemarks.push(remark);
      // goto next remark
      ++i;
    } else if (comparePosition(remark.from, entry.to) < 0) {
      // skip remark if it's inside the first entry
      ++i;
    } else {
      // goto next entry
      ++j;
    }
  }
}

function comparePosition(lhs, rhs) {
  const leftLine = lhs.line, rightLine = rhs.line;
  if (leftLine < rightLine) {
    return -1;
  } else if (leftLine > rightLine) {
    return 1;
  } else {
    const leftColumn = lhs.column, rightColumn = rhs.column;
    if (leftColumn <= rightColumn) {
      return -1;
    } else if (leftColumn > rightColumn) {
      return 1;
    } else {
      return 0;
    }
  }
}