
# R to S-expressions converter

# version 0.6

# Copyright (2011) "R to Clojure conversion project". All rights reserved.

# Redistribution and use in source and binary forms, with or without modification, are
# permitted provided that the following conditions are met:

#  1. Redistributions of source code must retain the above copyright notice, this list of
#         conditions and the following disclaimer.

#	    2. Redistributions in binary form must reproduce the above copyright notice, this list
#	          of conditions and the following disclaimer in the documentation and/or other materials
#		        provided with the distribution.

#			THIS SOFTWARE IS PROVIDED BY "R to Clojure conversion project" ''AS IS'' AND ANY EXPRESS OR IMPLIED
#			WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
#			FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL "R to Clojure conversion project" OR
#			CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
#			CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
#			SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
#			ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
#			NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN #IF
#			ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#			The views and conclusions contained in the software and documentation are those of the
#			authors and should not be interpreted as representing official policies, either expressed
#			or implied, of "R to Clojure conversion project".

copyright = "R to Clojure conversion project"
license = "FreeBSD license aka Simplified BSD license aka 2-clause BSD license"

# TO DO:
#   1. Figure out what to do with the bug, where 
#      parse.to.sexp(file<-"copy-R2Sexp.R")
#      is handled correctly, but
#      parse.to.sexp(file="copy-R2Sexp.R") 
#      produces an incorrect S-expr.
#
#   2. Do we need to include niceties, like comments,
#      eventually?
#
#   3. This does not include context, such as bindings
#      of variables.
#
#   4. The current version uses [] instead of ()
#      to better accomodate the needs of Clojure.

print.offset <- function(offset=0) {
  for(o in rep(NA,offset)) cat(" ")
}

as.sexp.rcode <- function(language.construct, offset = 0) {
  print.offset(offset)
  cat("[")
  l = as.list(language.construct)
  if (length(l) > 1) {
    child.number = 0
    for (child.expr in l) {
      child.number = child.number + 1
      if (child.number == 1) {
        cat(":")
        if (typeof(child.expr) == "symbol") {
          if (exists(as.character(child.expr))) {
            functype = typeof(eval(child.expr))
          } else {
            functype = "user-defined"
          }
          if (functype == "special") {
            cat("special-form")
          } else if (functype == "builtin") {
            cat("call-builtin")
          } else if (functype == "closure") {
            cat("call-closure")
          } else if (functype == "user-defined") {
            cat("call-user-defined")
          } else {
            cat("unknown-junk")
          }
        } else {
          cat("on-the-fly")
        }
      }
      cat("\n")
      if (typeof(child.expr) == "pairlist") {
        print.offset(offset+2)
        cat("[:params")
        cat("\n")
        atr = attributes(child.expr)
        atr.actual = atr$names
        atr.list = strsplit(atr.actual, " ")
        for (a in atr.list) {
          print.offset(offset+4)
          cat("[:arg \"")
          cat(a)
          cat("\"")
          default.present = TRUE
          if (typeof(child.expr[[a]]) == "symbol") {
            if (deparse(child.expr[[a]]) == "") {
              default.present = FALSE
            }
          }
          if (default.present) {
            cat(" :default\n")
            as.sexp.rcode(child.expr[[a]], offset+6)
            cat("\n")
            print.offset(offset+4)
          }
          cat("]\n")
        }
        print.offset(offset+2)
        cat("]")
      } else {
        as.sexp.rcode(child.expr, offset+2)
      }
    }
    cat("\n")
    print.offset(offset)
    cat("]")
  } else {
    for(s in l) { # single element list
      #cat(typeof(s), " ")
      t = typeof(s)
      b = (t == "symbol")
      if (t == "symbol") {
        if (strsplit(deparse(s, backtick = TRUE), NULL)[[1]][[1]] == "`") {
          t = "op"
        }
      }
      cat(":")
      cat(t)
      cat(" ")
      if (b) cat("\"")
      if (t == "character") {
        cat(encodeString(s, quote="\""))
      } else {
        normalize.assignment = FALSE
        if (t == "op")
          if (as.character(s) == "=" || as.character(s) == "<<-")
            normalize.assignment = TRUE 
        if (normalize.assignment) {
          cat("<-")
        } else {
          cat(s)
        }
      }
      if (b) cat("\"")
    }
    cat("]")
  }
}

as.sexp.rtoplevel <- function(parse.result) {
  for (top.level.expr in as.list(parse.result)) {
    print(top.level.expr)
    cat("\n")
    as.sexp.rcode(top.level.expr)
    cat("\n")
    cat("\n")
  }
}

parse.to.sexp <- function(file = "", n = NULL, text = NULL, 
                          prompt = "?") { # 2 more args should be added: , srcfile, encoding = "unknown") {
  # parse.result = parse(file,n,text,prompt,srcfile,encoding) -- we don't know yet
  #                                                          how to use the last 2 agrs right
  parse.result = parse(file,n,text,prompt)
  as.sexp.rtoplevel(parse.result)
}

#parse.to.sexp(text="x<-1+2; y<-x+5; z=y+4")
#parse.to.sexp(file<-"copy-R2Sexp.R")
parse.to.sexp(file<-"test.R")
#parse.to.sexp(text=".C(\"foo\", n<-as.integer(5), x<-as.double(rnorm(5)))")
#parse.to.sexp(text="c(1,2+3,4)")
#parse.to.sexp(text="if (2 == 3) {parse(\"a+b\")}")
#parse.to.sexp(text="x<-2; x=2; x<<-2; 2->x; 2->>x")
