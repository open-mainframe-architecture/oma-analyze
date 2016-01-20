"use strict";

var babylon = require('babylon');
var constants = require('oma-constants');
var traverse = require('babel-traverse').default;
var util = require('oma-util');

var AST = require('babel-types');

module.exports = function (archivePath, output) {
  return util.unzip(archivePath)
    .then(function (archive) {
      // collect class scripts of modules
      var readingClasses = [];
      var modules = archive.modules = {};
      for (var entry in archive.entries) {
        var moduleName = entry.substring(0, entry.indexOf('/'));
        if (moduleName.indexOf('.') > 0) {
          var classHome = moduleName + '/' + constants.module.classScripts.home;
          if (util.startsWith(entry, classHome)) {
            var classes = modules[moduleName] || (modules[moduleName] = {});
            var classPath = entry.substring(classHome.length + 1, entry.length - 3);
            var className = classPath.replace(util.vseps, '.');
            readingClasses.push(readClassScript(archive, entry, classes, className));
          }
        }
      }
      // when all class scripts have been read, forget about the archive and other assets
      return Promise.all(readingClasses).then(function () { return modules; })
    })
    .then(function (modules) {
      // use synchronous calls to analyze class scripts
      var analysis_ = {};
      for (var moduleName in modules) {
        var classes = modules[moduleName];
        if (util.hasEnumerables(classes)) {
          var moduleAnalysis_ = {};
          for (var className in classes) {
            var scriptSource = classes[className];
            moduleAnalysis_[className] = analyzeClass(moduleName, className, scriptSource);
          }
          analysis_[moduleName] = { _: moduleAnalysis_ };
        }
      }
      var analysisSource = JSON.stringify({ _: analysis_ }, null, '\t');
      return util.copy(util.streamInput(analysisSource), output);
    })
    ;
}

function readClassScript(archive, entry, classes, className) {
  return util.unzipText(archive.file, archive.entries[entry])
    .then(function (scriptSource) { classes[className] = scriptSource; })
    ;
}

function visitedClass(visitor) {
  // module and class combination
  return '~' + visitor.moduleName + '/' + visitor.className;
}

function scriptSides(functionParams) {
  var names = {};
  for (var i = 0; i < 2; ++i) {
    var param = functionParams[i];
    var name = param && param.type === 'Identifier' ? param.name : '';
    // first parameter is instance side, second is class side
    names[name] = !i;
  }
  return names;
}

function sideName(matchedKeyword) {
  return matchedKeyword.instanceSide ? 'instance' : 'class';
}

function literalOffset(matchedKeyword, node) {
  return { outer: matchedKeyword.literal.start, start: node.start, end: node.end };
}

function classAspect(analysis, name) {
  return analysis[name] || (analysis[name] = { _: {} });
}

function addSimpleAnalysis(analysis, name, matchedKeyword, key, node) {
  classAspect(analysis, name)._[key] = literalOffset(matchedKeyword, node);
}

function addFlagAnalysis(analysis, matchedKeyword, key, node, value) {
  classAspect(analysis, 'flags')._[key] = {
    boolean: value,
    offset: literalOffset(matchedKeyword, node)
  };
}

var ClassVisitor = {
  Program: function (astPath) {
    if (astPath.node.body.length > 1) {
      throw new Error('Too many statements: ' + visitedClass(this));
    }
  },
  'FunctionDeclaration|FunctionExpression': function (astPath) {
    if (!this.matchedScript) {
      // matched function (I, We) { }
      this.analysis.super = 'super';
      this.scriptArguments = scriptSides(astPath.node.params);
      this.matchedScript = true;
    }
  },
  CallExpression: {
    enter: function (astPath) {
      var node = astPath.node, callee = node.callee, args = node.arguments;
      if (!this.matchedScript) {
        // match 'SuperExpression'.subclass(function(I, We) { })
        var script = args[args.length - 1];
        if (!AST.isMemberExpression(callee) || !AST.isStringLiteral(callee.object)
          || callee.computed || callee.property.name !== 'subclass'
          || !args.length || !AST.isFunctionExpression(script)) {
          throw new Error('Bad script: ' + visitedClass(this));
        }
        this.analysis.super = callee.object.value;
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
          instanceSide: this.scriptArguments[callee.object.name],
          keyword: callee.property.name
        };
      }
    },
    exit: function (astPath) {
      var matchedKeyword = this.matchedKeyword;
      if (matchedKeyword && matchedKeyword.callSite === astPath.node) {
        // start to look for next keyword
        this.matchedKeyword = false;
      }
    }
  },
  ObjectMember: function (astPath) {
    var matched = this.matchedKeyword, node = astPath.node;
    if (matched && matched.literal === astPath.parent && !node.computed) {
      var key = node.key.name, analysis = this.analysis, value = node.value;
      var keyword = matched.keyword;
      switch (keyword) {
        case 'nest':
          // traverse nested class with nested visitor
          var nestedClasses = classAspect(analysis, 'nested');
          var nestedAnalysis = nestedClasses._[key] = {};
          astPath.traverse(ClassVisitor, {
            className: this.className + '._.' + key,
            moduleName: this.moduleName,
            analysis: nestedAnalysis
          });
          break;
        case 'am':
          // boolean flags
          if (!AST.isBooleanLiteral(value)) {
            throw new Error('Bad flag: ' + key + ' in ' + visitedClass(this));
          }
          addFlagAnalysis(analysis, matched, key, node, value.value);
          break;
        case 'have':
          // instance/class variables
          addSimpleAnalysis(analysis, sideName(matched) + 'Variables', matched, key, node);
          break;
        case 'access':
          // instance/class accessors
          addSimpleAnalysis(analysis, sideName(matched) + 'Accessors', matched, key, node);
          break;
        case 'know':
          if (AST.isNullLiteral(value)) {
            // instance/class constants
            addSimpleAnalysis(analysis, sideName(matched) + 'Constants', matched, key, node);
          } else {
            // instance/class methods
            addSimpleAnalysis(analysis, sideName(matched) + 'Methods', matched, key, node);
          }
          break;
        case 'setup':
        case 'share':
          // package constants and subroutines
          addSimpleAnalysis(analysis, 'package', matched, key, node);
          break;
        default:
          // collect unknown aspect of instance or class side
          var sideAnalysis = classAspect(analysis, sideName(matched));
          classAspect(sideAnalysis._, keyword)._[key] = literalOffset(matched, node);
      }
    }
  }
};

function analyzeClass(moduleName, className, scriptSource) {
  var classAnalysis = {};
  var state = {
    moduleName: moduleName,
    className: className,
    analysis: classAnalysis
  };
  var ast = babylon.parse(scriptSource);
  traverse(ast, ClassVisitor, null, state);
  var annotations_ = {};
  ast.comments
    .filter(function (comment) {
      return comment.value.length > 1 && comment.value.charAt(0) === '@';
    })
    .forEach(function (comment) {
      annotations_[comment.start] = comment.value;
    })
  ;
  if (util.hasEnumerables(annotations_)) {
    classAnalysis.annotations = { _: annotations_ };
  }
  return classAnalysis;
}