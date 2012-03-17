<?xml version='1.0' encoding='UTF-8'?>

<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
  <!-- XSLTXT (https://xsltxt.dev.java.net/) stylesheet taking -->
  <!-- XML terms, formulas and types to less verbose format. -->
  <!-- To produce standard XSLT from this do e.g.: -->
  <!-- java -jar xsltxt.jar toXSL miz.xsltxt >miz.xsl -->
  <!-- Then e.g.: xalan -XSL miz.xsl <ordinal2.pre >ordinal2.pre1 -->
  <!-- TODO: number B vars in fraenkel -->
  <!-- handle F and H parenthesis as K parenthesis -->
  <!-- numbers for Deffunc, Defpred -->
  <!-- article numbering in Ref? -->
  <!-- absolute definiens numbers for thesisExpansions? -->
  <!-- do not display BlockThesis for Proof? -->
  <!-- add @nr to canceled -->
  <!-- Constructor should know its serial number! - needed in defs -->
  <!-- possibly also article? -->
  <!-- change globally 'G' to 'L' for types? -> then change the -->
  <!-- hacks here and in emacs.el -->
  <!-- display definiens? -->
  <!-- NOTES: constructor disambiguation is done using the absolute numbers -->
  <!-- (attribute 'nr' and 'aid' of the Constructor element. -->
  <!-- This info for Constructors not defined in the article is -->
  <!-- taken from the .atr file (see variable $constrs) -->
  <xsl:output method="html"/>
  <!-- keys for fast constructor and reference lookup -->
  <xsl:key name="M" match="Constructor[@kind=&apos;M&apos;]" use="@relnr"/>
  <xsl:key name="L" match="Constructor[@kind=&apos;L&apos;]" use="@relnr"/>
  <xsl:key name="V" match="Constructor[@kind=&apos;V&apos;]" use="@relnr"/>
  <xsl:key name="R" match="Constructor[@kind=&apos;R&apos;]" use="@relnr"/>
  <xsl:key name="K" match="Constructor[@kind=&apos;K&apos;]" use="@relnr"/>
  <xsl:key name="U" match="Constructor[@kind=&apos;U&apos;]" use="@relnr"/>
  <xsl:key name="G" match="Constructor[@kind=&apos;G&apos;]" use="@relnr"/>
  <xsl:key name="T" match="/Theorems/Theorem[@kind=&apos;T&apos;]" use="concat(@articlenr,&apos;:&apos;,@nr)"/>
  <xsl:key name="D" match="/Theorems/Theorem[@kind=&apos;D&apos;]" use="concat(@articlenr,&apos;:&apos;,@nr)"/>
  <xsl:key name="S" match="/Schemes/Scheme" use="concat(@articlenr,&apos;:&apos;,@nr)"/>
  <!-- patterns are slightly tricky, since a predicate pattern -->
  <!-- may be linked to an attribute constructor; hence the -->
  <!-- indexing is done according to @constrkind and not @kind -->
  <!-- TODO: the attribute<->predicate change should propagate to usage -->
  <!-- of "is" -->
  <xsl:key name="P_M" match="Pattern[@constrkind=&apos;M&apos;]" use="@constrnr"/>
  <xsl:key name="P_L" match="Pattern[@constrkind=&apos;L&apos;]" use="@constrnr"/>
  <xsl:key name="P_V" match="Pattern[@constrkind=&apos;V&apos;]" use="@constrnr"/>
  <xsl:key name="P_R" match="Pattern[@constrkind=&apos;R&apos;]" use="@constrnr"/>
  <xsl:key name="P_K" match="Pattern[@constrkind=&apos;K&apos;]" use="@constrnr"/>
  <xsl:key name="P_U" match="Pattern[@constrkind=&apos;U&apos;]" use="@constrnr"/>
  <xsl:key name="P_G" match="Pattern[@constrkind=&apos;G&apos;]" use="@constrnr"/>
  <xsl:key name="F" match="Format" use="@nr"/>
  <xsl:key name="D_G" match="Symbol[@kind=&apos;G&apos;]" use="@nr"/>
  <xsl:key name="D_K" match="Symbol[@kind=&apos;K&apos;]" use="@nr"/>
  <xsl:key name="D_J" match="Symbol[@kind=&apos;J&apos;]" use="@nr"/>
  <xsl:key name="D_L" match="Symbol[@kind=&apos;L&apos;]" use="@nr"/>
  <xsl:key name="D_M" match="Symbol[@kind=&apos;M&apos;]" use="@nr"/>
  <xsl:key name="D_O" match="Symbol[@kind=&apos;O&apos;]" use="@nr"/>
  <xsl:key name="D_R" match="Symbol[@kind=&apos;R&apos;]" use="@nr"/>
  <xsl:key name="D_U" match="Symbol[@kind=&apos;U&apos;]" use="@nr"/>
  <xsl:key name="D_V" match="Symbol[@kind=&apos;V&apos;]" use="@nr"/>
  <xsl:variable name="lcletters">
    <xsl:text>abcdefghijklmnopqrstuvwxyz</xsl:text>
  </xsl:variable>
  <xsl:variable name="ucletters">
    <xsl:text>ABCDEFGHIJKLMNOPQRSTUVWXYZ</xsl:text>
  </xsl:variable>
  <!-- name of current article (upper case) -->
  <xsl:param name="aname">
    <xsl:value-of select="string(/*/@aid)"/>
  </xsl:param>
  <!-- name of current article (lower case) -->
  <xsl:param name="anamelc">
    <xsl:value-of select="translate($aname, $ucletters, $lcletters)"/>
  </xsl:param>
  <!-- .atr file with imported constructors -->
  <xsl:param name="constrs">
    <xsl:value-of select="concat($anamelc, &apos;.atr&apos;)"/>
  </xsl:param>
  <!-- .eth file with imported theorems -->
  <xsl:param name="thms">
    <xsl:value-of select="concat($anamelc, &apos;.eth&apos;)"/>
  </xsl:param>
  <!-- .esh file with imported schemes -->
  <xsl:param name="schms">
    <xsl:value-of select="concat($anamelc, &apos;.esh&apos;)"/>
  </xsl:param>
  <!-- .eno file with imported patterns -->
  <xsl:param name="patts">
    <xsl:value-of select="concat($anamelc, &apos;.eno&apos;)"/>
  </xsl:param>
  <!-- .frx file with all (both imported and article's) formats -->
  <xsl:param name="formats">
    <xsl:value-of select="concat($anamelc, &apos;.frx&apos;)"/>
  </xsl:param>
  <!-- .dcx file with vocabulary -->
  <xsl:param name="vocs">
    <xsl:value-of select="concat($anamelc, &apos;.dcx&apos;)"/>
  </xsl:param>
  <!-- mmlquery address -->
  <xsl:param name="mmlq">
    <xsl:text>http://merak.pb.bialystok.pl/mmlquery/fillin.php?entry=</xsl:text>
  </xsl:param>
  <!-- tells whether relative or absolute names are shown -->
  <xsl:param name="relnames">
    <xsl:text>1</xsl:text>
  </xsl:param>
  <!-- linking methods: -->
  <!-- "q" - query, everything is linked to mmlquery -->
  <!-- "s" - self, everything is linked to these xml files -->
  <!-- "m" - mizaring, current article's constructs are linked to self, -->
  <!-- the rest is linked to mmlquery -->
  <xsl:param name="linking">
    <xsl:text>m</xsl:text>
  </xsl:param>
  <xsl:param name="varcolor">
    <xsl:text>Olive</xsl:text>
  </xsl:param>
  <xsl:param name="constcolor">
    <xsl:text>Maroon</xsl:text>
  </xsl:param>
  <xsl:param name="locicolor">
    <xsl:text>Maroon</xsl:text>
  </xsl:param>
  <xsl:param name="labcolor">
    <xsl:text>Green</xsl:text>
  </xsl:param>
  <!-- number of parenthesis colors (see the stylesheet in the bottom) -->
  <xsl:param name="pcolors_nr">
    <xsl:text>6</xsl:text>
  </xsl:param>

  <!-- Formulas -->
  <!-- #i is nr of the bound variable, 1 by default -->
  <!-- #k is start of the sequence of vars with the same type, $i by default -->
  <!-- we now output only one typing for such sequences -->
  <xsl:template match="For">
    <xsl:param name="i"/>
    <xsl:param name="k"/>
    <xsl:variable name="j">
      <xsl:choose>
        <xsl:when test="$i">
          <xsl:value-of select="$i"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>1</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="l">
      <xsl:choose>
        <xsl:when test="$k">
          <xsl:value-of select="$k"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$j"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="nm">
      <xsl:value-of select="name(*[2])"/>
    </xsl:variable>
    <xsl:choose>
      <xsl:when test="($nm = &quot;For&quot;) and (*[1]/@nr = *[2]/*[1]/@nr) 
      and (string(*[1]) = string(*[2]/*[1]))">
        <xsl:apply-templates select="*[2]">
          <xsl:with-param name="i" select="$j+1"/>
          <xsl:with-param name="k" select="$l"/>
        </xsl:apply-templates>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>for </xsl:text>
        <xsl:call-template name="ft_list">
          <xsl:with-param name="f" select="$l"/>
          <xsl:with-param name="t" select="$j"/>
          <xsl:with-param name="sep">
            <xsl:text>, </xsl:text>
          </xsl:with-param>
        </xsl:call-template>
        <xsl:text> being</xsl:text>
        <xsl:apply-templates select="*[1]"/>
        <xsl:if test="not(($nm = &quot;For&quot;))">
          <xsl:text> holds </xsl:text>
        </xsl:if>
        <xsl:if test="not(($nm = &quot;Pred&quot;))">
          <xsl:element name="br"/>
        </xsl:if>
        <xsl:apply-templates select="*[2]">
          <xsl:with-param name="i" select="$j+1"/>
        </xsl:apply-templates>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- tpl [And/For] { <div {"for B being"; apply[*[1]]; -->
  <!-- " holds "; <div { @class="add";  apply[*[2]]; } } } -->
  <xsl:template match="Not">
    <xsl:param name="i"/>
    <xsl:text>not </xsl:text>
    <xsl:apply-templates select="*[1]">
      <xsl:with-param name="i" select="$i"/>
    </xsl:apply-templates>
  </xsl:template>

  <!-- tpl [And/Not] { if [For] { <div { "not "; apply[*[1]]; } } -->
  <!-- else { "not "; apply[*[1]]; } } -->
  <xsl:template match="And">
    <xsl:param name="i"/>
    <xsl:text>( </xsl:text>
    <xsl:call-template name="ilist">
      <xsl:with-param name="separ">
        <xsl:text> &amp; </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="*"/>
      <xsl:with-param name="i" select="$i"/>
    </xsl:call-template>
    <xsl:text> )</xsl:text>
  </xsl:template>

  <xsl:template match="Pred">
    <xsl:param name="i"/>
    <xsl:choose>
      <xsl:when test="@kind=&apos;P&apos;">
        <xsl:text>P</xsl:text>
        <xsl:value-of select="@nr"/>
        <xsl:text>[</xsl:text>
        <xsl:call-template name="list">
          <xsl:with-param name="separ">
            <xsl:text>,</xsl:text>
          </xsl:with-param>
          <xsl:with-param name="elems" select="*"/>
        </xsl:call-template>
        <xsl:text>]</xsl:text>
      </xsl:when>
      <xsl:when test="@kind=&apos;V&apos;">
        <xsl:apply-templates select="*[position() = last()]"/>
        <xsl:text> is </xsl:text>
        <xsl:call-template name="abs">
          <xsl:with-param name="k" select="@kind"/>
          <xsl:with-param name="nr" select="@nr"/>
          <xsl:with-param name="sym">
            <xsl:call-template name="abs1">
              <xsl:with-param name="k" select="@kind"/>
              <xsl:with-param name="nr" select="@nr"/>
            </xsl:call-template>
          </xsl:with-param>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="pp">
          <xsl:with-param name="k" select="@kind"/>
          <xsl:with-param name="nr" select="@nr"/>
          <xsl:with-param name="args" select="*"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- ,#sym1=abs(#k=`@kind`, #nr=`@nr`, #sym=abs1(#k=`@kind`, #nr=`@nr`))); }} -->
  <!-- "[ "; list(#separ=",", #elems=`*`); "]"; } -->
  <xsl:template match="PrivPred">
    <xsl:param name="i"/>
    <xsl:text>S</xsl:text>
    <xsl:value-of select="@nr"/>
    <xsl:text>[</xsl:text>
    <xsl:call-template name="list">
      <xsl:with-param name="separ">
        <xsl:text>,</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="*[position() &lt; last()]"/>
    </xsl:call-template>
    <xsl:text>]</xsl:text>
  </xsl:template>

  <xsl:template match="Is">
    <xsl:param name="i"/>
    <xsl:apply-templates select="*[1]"/>
    <xsl:text> is </xsl:text>
    <xsl:apply-templates select="*[2]"/>
  </xsl:template>

  <xsl:template match="Verum">
    <xsl:param name="i"/>
    <xsl:text>verum</xsl:text>
  </xsl:template>

  <xsl:template match="ErrorFrm">
    <xsl:param name="i"/>
    <xsl:text>errorfrm</xsl:text>
  </xsl:template>

  <!-- Terms -->
  <!-- #p is the parenthesis count -->
  <xsl:template match="Var">
    <xsl:param name="p"/>
    <xsl:call-template name="pvar">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
  </xsl:template>

  <xsl:template match="LocusVar">
    <xsl:param name="p"/>
    <xsl:call-template name="ploci">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
  </xsl:template>

  <xsl:template match="FreeVar">
    <xsl:param name="p"/>
    <xsl:text>X</xsl:text>
    <xsl:value-of select="@nr"/>
  </xsl:template>

  <xsl:template match="Const">
    <xsl:param name="p"/>
    <xsl:call-template name="pconst">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
  </xsl:template>

  <xsl:template match="InfConst">
    <xsl:param name="p"/>
    <xsl:text>D</xsl:text>
    <xsl:value-of select="@nr"/>
  </xsl:template>

  <xsl:template match="Num">
    <xsl:param name="p"/>
    <xsl:value-of select="@nr"/>
  </xsl:template>

  <xsl:template match="Func">
    <xsl:param name="p"/>
    <xsl:choose>
      <xsl:when test="@kind=&apos;F&apos;">
        <xsl:text>F</xsl:text>
        <xsl:value-of select="@nr"/>
        <xsl:text>(</xsl:text>
        <xsl:call-template name="list">
          <xsl:with-param name="separ">
            <xsl:text>,</xsl:text>
          </xsl:with-param>
          <xsl:with-param name="elems" select="*"/>
        </xsl:call-template>
        <xsl:text>)</xsl:text>
      </xsl:when>
      <xsl:when test="@kind=&apos;U&apos;">
        <xsl:text>the </xsl:text>
        <xsl:call-template name="abs">
          <xsl:with-param name="k" select="@kind"/>
          <xsl:with-param name="nr" select="@nr"/>
          <xsl:with-param name="sym">
            <xsl:call-template name="abs1">
              <xsl:with-param name="k" select="@kind"/>
              <xsl:with-param name="nr" select="@nr"/>
            </xsl:call-template>
          </xsl:with-param>
        </xsl:call-template>
        <xsl:text> of </xsl:text>
        <xsl:apply-templates select="*[position() = last()]">
          <xsl:with-param name="p" select="$p"/>
        </xsl:apply-templates>
      </xsl:when>
      <xsl:otherwise>
        <xsl:variable name="par">
          <xsl:choose>
            <xsl:when test="$p&gt;0">
              <xsl:value-of select="$p+1"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:choose>
                <xsl:when test="name(..)=&apos;Func&apos;">
                  <xsl:text>1</xsl:text>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:text>0</xsl:text>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:call-template name="pp">
          <xsl:with-param name="k" select="@kind"/>
          <xsl:with-param name="nr" select="@nr"/>
          <xsl:with-param name="args" select="*"/>
          <xsl:with-param name="parenth" select="$par"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="PrivFunc">
    <xsl:param name="p"/>
    <xsl:text>H</xsl:text>
    <xsl:value-of select="@nr"/>
    <xsl:text>(</xsl:text>
    <xsl:call-template name="list">
      <xsl:with-param name="separ">
        <xsl:text>,</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="*[position()&gt;1]"/>
    </xsl:call-template>
    <xsl:text>)</xsl:text>
  </xsl:template>

  <xsl:template match="ErrorTrm">
    <xsl:param name="p"/>
    <xsl:text>errortrm</xsl:text>
  </xsl:template>

  <xsl:template match="Fraenkel">
    <xsl:param name="p"/>
    <xsl:variable name="par">
      <xsl:choose>
        <xsl:when test="$p&gt;0">
          <xsl:value-of select="$p+1"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>1</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="paren_color" select="$par mod $pcolors_nr"/>
    <xsl:element name="span">
      <xsl:attribute name="class">
        <xsl:value-of select="concat(&quot;paren&quot;,$paren_color)"/>
      </xsl:attribute>
      <xsl:text>{</xsl:text>
      <xsl:element name="span">
        <xsl:attribute name="class">
          <xsl:text>default</xsl:text>
        </xsl:attribute>
        <xsl:text> </xsl:text>
        <xsl:apply-templates select="*[position() = last() - 1]">
          <xsl:with-param name="p" select="$par"/>
        </xsl:apply-templates>
        <xsl:if test="count(*)&gt;2">
          <xsl:text> where B is </xsl:text>
          <xsl:call-template name="list">
            <xsl:with-param name="separ">
              <xsl:text>, B is </xsl:text>
            </xsl:with-param>
            <xsl:with-param name="elems" select="*[position() &lt; last() - 1]"/>
          </xsl:call-template>
        </xsl:if>
        <xsl:text> : </xsl:text>
        <xsl:apply-templates select="*[position() = last()]"/>
        <xsl:text> </xsl:text>
      </xsl:element>
      <xsl:text>}</xsl:text>
    </xsl:element>
    <xsl:text> </xsl:text>
  </xsl:template>

  <!-- Types -->
  <xsl:template match="Typ">
    <xsl:text> </xsl:text>
    <xsl:if test="count(*)&gt;0">
      <xsl:apply-templates select="*[1]"/>
    </xsl:if>
    <xsl:choose>
      <xsl:when test="@kind=&quot;M&quot;">
        <xsl:call-template name="pp">
          <xsl:with-param name="k">
            <xsl:text>M</xsl:text>
          </xsl:with-param>
          <xsl:with-param name="nr" select="@nr"/>
          <xsl:with-param name="args" select="*[position()&gt;2]"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="@kind=&quot;G&quot;">
            <xsl:call-template name="abs">
              <xsl:with-param name="k">
                <xsl:text>L</xsl:text>
              </xsl:with-param>
              <xsl:with-param name="nr" select="@nr"/>
              <xsl:with-param name="sym">
                <xsl:call-template name="abs1">
                  <xsl:with-param name="k">
                    <xsl:text>G</xsl:text>
                  </xsl:with-param>
                  <xsl:with-param name="nr" select="@nr"/>
                </xsl:call-template>
              </xsl:with-param>
            </xsl:call-template>
            <xsl:if test="count(*)&gt;2">
              <xsl:text> of </xsl:text>
              <xsl:call-template name="list">
                <xsl:with-param name="separ">
                  <xsl:text>,</xsl:text>
                </xsl:with-param>
                <xsl:with-param name="elems" select="*[position()&gt;2]"/>
              </xsl:call-template>
            </xsl:if>
          </xsl:when>
          <xsl:otherwise>
            <xsl:value-of select="@kind"/>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- Clusters -->
  <xsl:template match="Cluster">
    <xsl:call-template name="list">
      <xsl:with-param name="separ">
        <xsl:text> </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="*"/>
    </xsl:call-template>
    <xsl:text> </xsl:text>
  </xsl:template>

  <!-- Adjective -->
  <xsl:template match="Adjective">
    <xsl:if test="@value=&quot;false&quot;">
      <xsl:text>non </xsl:text>
    </xsl:if>
    <xsl:call-template name="abs">
      <xsl:with-param name="k">
        <xsl:text>V</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="nr" select="@nr"/>
      <xsl:with-param name="sym">
        <xsl:call-template name="abs1">
          <xsl:with-param name="k">
            <xsl:text>V</xsl:text>
          </xsl:with-param>
          <xsl:with-param name="nr" select="@nr"/>
        </xsl:call-template>
      </xsl:with-param>
    </xsl:call-template>
  </xsl:template>

  <!-- if [count(*)>0] { "("; list(#separ=",", #elems=`*`); ")"; }} -->
  <xsl:template match="Proposition">
    <xsl:if test="@nr&gt;0">
      <xsl:call-template name="plab">
        <xsl:with-param name="nr" select="@nr"/>
      </xsl:call-template>
      <xsl:text>: </xsl:text>
    </xsl:if>
    <xsl:apply-templates/>
    <xsl:text> </xsl:text>
  </xsl:template>

  <!-- Justifications -->
  <xsl:template match="By	">
    <xsl:if test="(@linked=&quot;true&quot;) or (count(*)&gt;0)">
      <xsl:element name="b">
        <xsl:text>by </xsl:text>
      </xsl:element>
    </xsl:if>
    <xsl:element name="i">
      <xsl:if test="@linked=&quot;true&quot;">
        <xsl:text>previous</xsl:text>
      </xsl:if>
      <xsl:if test="count(*)&gt;0">
        <xsl:if test="@linked=&quot;true&quot;">
          <xsl:text>, </xsl:text>
        </xsl:if>
        <xsl:call-template name="list">
          <xsl:with-param name="separ">
            <xsl:text>, </xsl:text>
          </xsl:with-param>
          <xsl:with-param name="elems" select="*"/>
        </xsl:call-template>
      </xsl:if>
      <xsl:text>;</xsl:text>
      <xsl:element name="br"/>
    </xsl:element>
  </xsl:template>

  <xsl:template match="IterStep/By">
    <xsl:if test="(@linked=&quot;true&quot;) or (count(*)&gt;0)">
      <xsl:element name="b">
        <xsl:text>by </xsl:text>
      </xsl:element>
    </xsl:if>
    <xsl:element name="i">
      <xsl:if test="@linked=&quot;true&quot;">
        <xsl:text>previous</xsl:text>
      </xsl:if>
      <xsl:if test="count(*)&gt;0">
        <xsl:if test="@linked=&quot;true&quot;">
          <xsl:text>, </xsl:text>
        </xsl:if>
        <xsl:call-template name="list">
          <xsl:with-param name="separ">
            <xsl:text>, </xsl:text>
          </xsl:with-param>
          <xsl:with-param name="elems" select="*"/>
        </xsl:call-template>
      </xsl:if>
    </xsl:element>
  </xsl:template>

  <xsl:template match="From">
    <xsl:element name="b">
      <xsl:text>from </xsl:text>
    </xsl:element>
    <xsl:element name="i">
      <xsl:call-template name="getschref">
        <xsl:with-param name="anr" select="@articlenr"/>
        <xsl:with-param name="nr" select="@nr"/>
      </xsl:call-template>
      <xsl:text>(</xsl:text>
      <xsl:call-template name="list">
        <xsl:with-param name="separ">
          <xsl:text>, </xsl:text>
        </xsl:with-param>
        <xsl:with-param name="elems" select="*"/>
      </xsl:call-template>
      <xsl:text>)</xsl:text>
      <xsl:text>;</xsl:text>
      <xsl:element name="br"/>
    </xsl:element>
  </xsl:template>

  <xsl:template match="IterStep/From">
    <xsl:element name="b">
      <xsl:text>from </xsl:text>
    </xsl:element>
    <xsl:element name="i">
      <xsl:call-template name="getschref">
        <xsl:with-param name="anr" select="@articlenr"/>
        <xsl:with-param name="nr" select="@nr"/>
      </xsl:call-template>
      <xsl:text>(</xsl:text>
      <xsl:call-template name="list">
        <xsl:with-param name="separ">
          <xsl:text>, </xsl:text>
        </xsl:with-param>
        <xsl:with-param name="elems" select="*"/>
      </xsl:call-template>
      <xsl:text>)</xsl:text>
    </xsl:element>
  </xsl:template>

  <xsl:template match="Ref">
    <xsl:choose>
      <xsl:when test="not(@articlenr)">
        <xsl:call-template name="plab">
          <xsl:with-param name="nr" select="@nr"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="getref">
          <xsl:with-param name="k" select="@kind"/>
          <xsl:with-param name="anr" select="@articlenr"/>
          <xsl:with-param name="nr" select="@nr"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="ErrorInf">
    <xsl:text>errorinference;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="IterStep/ErrorInf">
    <xsl:text>errorinference</xsl:text>
  </xsl:template>

  <xsl:template match="SkippedProof">
    <xsl:text>skippedproof;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="IterStep/SkippedProof">
    <xsl:text>skippedproof</xsl:text>
  </xsl:template>

  <!-- Term, elIterStep+ -->
  <xsl:template match="IterEquality">
    <xsl:if test="@nr&gt;0">
      <xsl:call-template name="plab">
        <xsl:with-param name="nr" select="@nr"/>
      </xsl:call-template>
      <xsl:text>: </xsl:text>
    </xsl:if>
    <xsl:apply-templates select="*[1]"/>
    <xsl:text> = </xsl:text>
    <xsl:call-template name="nlist">
      <xsl:with-param name="separ">
        <xsl:text>.= </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="IterStep"/>
    </xsl:call-template>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="IterStep">
    <xsl:apply-templates/>
  </xsl:template>

  <!-- Skeleton steps -->
  <xsl:template match="Let">
    <xsl:variable name="j" select="@nr"/>
    <xsl:element name="b">
      <xsl:text>let </xsl:text>
    </xsl:element>
    <xsl:call-template name="pconst">
      <xsl:with-param name="nr" select="$j"/>
    </xsl:call-template>
    <xsl:text> be </xsl:text>
    <xsl:call-template name="jlist">
      <xsl:with-param name="j" select="$j"/>
      <xsl:with-param name="sep1">
        <xsl:text>, </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="sep2">
        <xsl:text> be </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="*"/>
    </xsl:call-template>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="Assume">
    <xsl:element name="b">
      <xsl:text>assume </xsl:text>
    </xsl:element>
    <xsl:if test="count(*)&gt;1">
      <xsl:text>that </xsl:text>
    </xsl:if>
    <xsl:call-template name="nlist">
      <xsl:with-param name="separ">
        <xsl:text>and </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="*"/>
    </xsl:call-template>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="Given">
    <xsl:variable name="j" select="@nr"/>
    <xsl:element name="b">
      <xsl:text>given </xsl:text>
    </xsl:element>
    <xsl:call-template name="pconst">
      <xsl:with-param name="nr" select="$j"/>
    </xsl:call-template>
    <xsl:text> being </xsl:text>
    <xsl:call-template name="jlist">
      <xsl:with-param name="j" select="$j"/>
      <xsl:with-param name="sep1">
        <xsl:text>, </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="sep2">
        <xsl:text> being </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="Typ"/>
    </xsl:call-template>
    <xsl:text> such that </xsl:text>
    <xsl:call-template name="nlist">
      <xsl:with-param name="separ">
        <xsl:text>and </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="Proposition"/>
    </xsl:call-template>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="Take">
    <xsl:element name="b">
      <xsl:text>take </xsl:text>
    </xsl:element>
    <xsl:apply-templates/>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="TakeAsVar">
    <xsl:element name="b">
      <xsl:text>take </xsl:text>
    </xsl:element>
    <xsl:call-template name="pconst">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
    <xsl:text> = </xsl:text>
    <xsl:apply-templates select="*[2]"/>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="Conclusion">
    <xsl:element name="b">
      <xsl:text>thus </xsl:text>
    </xsl:element>
    <xsl:apply-templates/>
  </xsl:template>

  <xsl:template match="Case">
    <xsl:element name="b">
      <xsl:text>case </xsl:text>
    </xsl:element>
    <xsl:if test="count(*)&gt;1">
      <xsl:text>that </xsl:text>
    </xsl:if>
    <xsl:call-template name="nlist">
      <xsl:with-param name="separ">
        <xsl:text>and </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="*"/>
    </xsl:call-template>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="Suppose">
    <xsl:element name="b">
      <xsl:text>suppose </xsl:text>
    </xsl:element>
    <xsl:if test="count(*)&gt;1">
      <xsl:text>that </xsl:text>
    </xsl:if>
    <xsl:call-template name="nlist">
      <xsl:with-param name="separ">
        <xsl:text>and </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="*"/>
    </xsl:call-template>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="PerCases">
    <xsl:element name="b">
      <xsl:text>per cases </xsl:text>
    </xsl:element>
    <xsl:apply-templates/>
  </xsl:template>

  <!-- Auxiliary items -->
  <xsl:template match="Consider">
    <xsl:variable name="j" select="@nr"/>
    <xsl:element name="b">
      <xsl:text>consider </xsl:text>
    </xsl:element>
    <xsl:call-template name="pconst">
      <xsl:with-param name="nr" select="$j"/>
    </xsl:call-template>
    <xsl:text> being </xsl:text>
    <xsl:call-template name="jlist">
      <xsl:with-param name="j" select="$j"/>
      <xsl:with-param name="sep1">
        <xsl:text>, </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="sep2">
        <xsl:text> being </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="Typ"/>
    </xsl:call-template>
    <xsl:if test="count(Proposition) &gt; 1">
      <xsl:text> such that </xsl:text>
      <xsl:element name="br"/>
      <xsl:call-template name="nlist">
        <xsl:with-param name="separ">
          <xsl:text>and </xsl:text>
        </xsl:with-param>
        <xsl:with-param name="elems" select="Proposition[position() &gt; 1]"/>
      </xsl:call-template>
    </xsl:if>
    <xsl:apply-templates select="*[2]"/>
  </xsl:template>

  <xsl:template match="Reconsider">
    <xsl:variable name="j" select="@nr"/>
    <xsl:element name="b">
      <xsl:text>reconsider </xsl:text>
    </xsl:element>
    <xsl:call-template name="pconst">
      <xsl:with-param name="nr" select="$j"/>
    </xsl:call-template>
    <xsl:text> = </xsl:text>
    <xsl:call-template name="jlist">
      <xsl:with-param name="j" select="$j"/>
      <xsl:with-param name="sep1">
        <xsl:text>, </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="sep2">
        <xsl:text> = </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="*[(position() &gt; 1) 
                        and (position() &lt; (last() - 1))]"/>
    </xsl:call-template>
    <xsl:text> as </xsl:text>
    <xsl:apply-templates select="*[1]"/>
    <xsl:text> </xsl:text>
    <xsl:apply-templates select="*[last()]"/>
  </xsl:template>

  <xsl:template match="Set">
    <xsl:element name="b">
      <xsl:text>set </xsl:text>
    </xsl:element>
    <xsl:call-template name="pconst">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
    <xsl:text> = </xsl:text>
    <xsl:apply-templates select="*[1]"/>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="DefFunc">
    <xsl:element name="b">
      <xsl:text>deffunc</xsl:text>
    </xsl:element>
    <xsl:text> H(</xsl:text>
    <xsl:call-template name="list">
      <xsl:with-param name="separ">
        <xsl:text>,</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="ArgTypes/Typ"/>
    </xsl:call-template>
    <xsl:text>) </xsl:text>
    <xsl:element name="b">
      <xsl:text>-&gt; </xsl:text>
    </xsl:element>
    <xsl:apply-templates select="*[3]"/>
    <xsl:text> = </xsl:text>
    <xsl:apply-templates select="*[2]"/>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="DefPred">
    <xsl:element name="b">
      <xsl:text>defpred</xsl:text>
    </xsl:element>
    <xsl:text> S[</xsl:text>
    <xsl:call-template name="list">
      <xsl:with-param name="separ">
        <xsl:text>,</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="ArgTypes/Typ"/>
    </xsl:call-template>
    <xsl:text>] means </xsl:text>
    <xsl:apply-templates select="*[2]"/>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <!-- Thesis after skeleton item, with definiens numbers -->
  <xsl:template match="Thesis"/>

  <!-- "thesis: "; apply[*[1]]; " defs("; -->
  <!-- list(#separ=",", #elems=`ThesisExpansions/Pair[@x]`); -->
  <!-- ");"; <br; } -->
  <!-- Registrations -->
  <xsl:template match="RCluster">
    <xsl:element name="b">
      <xsl:text>cluster </xsl:text>
    </xsl:element>
    <xsl:choose>
      <xsl:when test="ErrorCluster">
        <xsl:text>errorcluster</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates select="*[3]"/>
        <xsl:text> </xsl:text>
        <xsl:apply-templates select="*[2]"/>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="CCluster">
    <xsl:element name="b">
      <xsl:text>cluster </xsl:text>
    </xsl:element>
    <xsl:choose>
      <xsl:when test="ErrorCluster">
        <xsl:text>errorcluster</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates select="*[2]"/>
        <xsl:element name="b">
          <xsl:text> -&gt; </xsl:text>
        </xsl:element>
        <xsl:apply-templates select="*[4]"/>
        <xsl:text> </xsl:text>
        <xsl:apply-templates select="*[3]"/>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="FCluster">
    <xsl:element name="b">
      <xsl:text>cluster </xsl:text>
    </xsl:element>
    <xsl:choose>
      <xsl:when test="ErrorCluster">
        <xsl:text>errorcluster</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates select="*[2]"/>
        <xsl:element name="b">
          <xsl:text> -&gt; </xsl:text>
        </xsl:element>
        <xsl:apply-templates select="*[3]"/>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <!-- Blocks -->
  <xsl:template match="BlockThesis"/>

  <!-- "blockthesis: "; apply; ";"; <br; } -->
  <!-- (  ( elBlockThesis, elCase, elThesis, Reasoning ) -->
  <!-- |  ( elCase, Reasoning, elBlockThesis ) ) -->
  <xsl:template match="CaseBlock">
    <xsl:element name="div">
      <xsl:apply-templates select="Case"/>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="*[not(name()=&apos;Case&apos;)]"/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <xsl:template match="SupposeBlock">
    <xsl:element name="div">
      <xsl:apply-templates select="Suppose"/>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="*[not(name()=&apos;Suppose&apos;)]"/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- (  ( elBlockThesis, ( elCaseBlock+ | elSupposeBlock+ ), -->
  <!-- elPerCases, elThesis, elEndPosition  ) -->
  <!-- |  ( ( elCaseBlock+ | elSupposeBlock+ ), -->
  <!-- elPerCases, elEndPosition, elBlockThesis ) ) -->
  <xsl:template match="PerCasesReasoning">
    <xsl:element name="div">
      <xsl:apply-templates select="PerCases"/>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="BlockThesis"/>
        <xsl:apply-templates select="Thesis"/>
        <xsl:apply-templates select="CaseBlock | SupposeBlock"/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- elBlockThesis, Reasoning -->
  <xsl:template match="Proof">
    <xsl:element name="div">
      <xsl:element name="b">
        <xsl:text>proof </xsl:text>
      </xsl:element>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- Reasoning, elBlockThesis -->
  <xsl:template match="Now">
    <xsl:element name="div">
      <xsl:element name="b">
        <xsl:text>now </xsl:text>
      </xsl:element>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="BlockThesis"/>
        <xsl:apply-templates select="*[not(name()=&apos;BlockThesis&apos;)]"/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- ignore them -->
  <xsl:template match="Reservation/Typ">
    <xsl:text/>
  </xsl:template>

  <xsl:template match="Definiens/*">
    <xsl:text/>
  </xsl:template>

  <xsl:template match="JustifiedTheorem">
    <xsl:element name="b">
      <xsl:text>theorem </xsl:text>
    </xsl:element>
    <xsl:for-each select="Proposition[@nr &gt; 0]">
      <xsl:call-template name="plab">
        <xsl:with-param name="nr" select="@nr"/>
      </xsl:call-template>
      <xsl:text>: </xsl:text>
    </xsl:for-each>
    <xsl:element name="br"/>
    <xsl:choose>
      <xsl:when test="Proof">
        <xsl:element name="div">
          <xsl:attribute name="class">
            <xsl:text>add</xsl:text>
          </xsl:attribute>
          <xsl:apply-templates select="*[1]/*[1]"/>
        </xsl:element>
        <xsl:apply-templates select="*[2]"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:element name="div">
          <xsl:attribute name="class">
            <xsl:text>add</xsl:text>
          </xsl:attribute>
          <xsl:apply-templates select="*[1]/*[1]"/>
          <xsl:text> </xsl:text>
          <xsl:apply-templates select="*[2]"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="DefTheorem">
    <xsl:element name="b">
      <xsl:text>deftheorem </xsl:text>
    </xsl:element>
    <xsl:for-each select="Proposition[@nr &gt; 0]">
      <xsl:call-template name="plab">
        <xsl:with-param name="nr" select="@nr"/>
      </xsl:call-template>
      <xsl:text>: </xsl:text>
    </xsl:for-each>
    <xsl:element name="br"/>
    <xsl:element name="div">
      <xsl:attribute name="class">
        <xsl:text>add</xsl:text>
      </xsl:attribute>
      <xsl:apply-templates select="*[1]/*[1]"/>
      <xsl:text>;</xsl:text>
    </xsl:element>
  </xsl:template>

  <!-- Property, elProposition, Justification -->
  <xsl:template match="JustifiedProperty">
    <xsl:element name="b">
      <xsl:value-of select="translate(name(*[1]), $ucletters, $lcletters)"/>
    </xsl:element>
    <xsl:element name="br"/>
    <xsl:apply-templates select="*[position()&gt;1]"/>
  </xsl:template>

  <!-- Formula | ( elProposition, Justification ) -->
  <xsl:template match="UnknownCorrCond|Coherence|Compatibility|Consistency|Existence|Uniqueness">
    <xsl:element name="b">
      <xsl:value-of select="translate(name(), $ucletters, $lcletters)"/>
    </xsl:element>
    <xsl:element name="br"/>
    <xsl:apply-templates/>
  </xsl:template>

  <!-- CorrectnessCondition*, elProposition, Justification -->
  <xsl:template match="Correctness">
    <xsl:element name="b">
      <xsl:text>correctness: </xsl:text>
    </xsl:element>
    <xsl:element name="br"/>
    <xsl:apply-templates/>
  </xsl:template>

  <xsl:template match="Canceled">
    <xsl:element name="b">
      <xsl:text>canceled;</xsl:text>
    </xsl:element>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="SchemeFuncDecl">
    <xsl:text>F</xsl:text>
    <xsl:value-of select="@nr"/>
    <xsl:text>(</xsl:text>
    <xsl:call-template name="list">
      <xsl:with-param name="separ">
        <xsl:text>,</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="ArgTypes/Typ"/>
    </xsl:call-template>
    <xsl:text>) </xsl:text>
    <xsl:element name="b">
      <xsl:text>-&gt; </xsl:text>
    </xsl:element>
    <xsl:apply-templates select="*[2]"/>
  </xsl:template>

  <xsl:template match="SchemePredDecl">
    <xsl:text>P</xsl:text>
    <xsl:value-of select="@nr"/>
    <xsl:text>[</xsl:text>
    <xsl:call-template name="list">
      <xsl:with-param name="separ">
        <xsl:text>,</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="ArgTypes/Typ"/>
    </xsl:call-template>
    <xsl:text>]</xsl:text>
  </xsl:template>

  <!-- ( elSchemeFuncDecl | elSchemePredDecl )*, -->
  <!-- element elSchemePremises { elProposition* }, -->
  <!-- elProposition, Justification, elEndPosition -->
  <xsl:template match="SchemeBlock">
    <xsl:element name="div">
      <xsl:element name="b">
        <xsl:text>scheme</xsl:text>
      </xsl:element>
      <xsl:text> s</xsl:text>
      <xsl:value-of select="@schemenr"/>
      <xsl:text>{ </xsl:text>
      <xsl:call-template name="list">
        <xsl:with-param name="separ">
          <xsl:text>, </xsl:text>
        </xsl:with-param>
        <xsl:with-param name="elems" select="SchemeFuncDecl|SchemePredDecl"/>
      </xsl:call-template>
      <xsl:text> } :</xsl:text>
      <xsl:element name="br"/>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="Proposition"/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>provided</xsl:text>
      </xsl:element>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:call-template name="list">
          <xsl:with-param name="separ">
            <xsl:text> and </xsl:text>
          </xsl:with-param>
          <xsl:with-param name="elems" select="SchemePremises/Proposition"/>
        </xsl:call-template>
      </xsl:element>
      <xsl:apply-templates select="*[position() = last() - 1]"/>
    </xsl:element>
  </xsl:template>

  <!-- ( ( CorrectnessCondition*, elCorrectness?, -->
  <!-- elJustifiedProperty*, elConstructor? ) -->
  <!-- | ( elConstructor, elConstructor, elConstructor+, -->
  <!-- CorrectnessCondition*, elCorrectness? )) -->
  <xsl:template match="Definition">
    <xsl:choose>
      <xsl:when test="@kind = &apos;G&apos;">
        <xsl:for-each select="Constructor[@kind=&quot;G&quot;]">
          <xsl:element name="a">
            <xsl:attribute name="NAME">
              <xsl:value-of select="concat(&quot;G&quot;,@nr)"/>
            </xsl:attribute>
            <xsl:element name="b">
              <xsl:text>aggr </xsl:text>
            </xsl:element>
          </xsl:element>
          <xsl:call-template name="abs">
            <xsl:with-param name="k">
              <xsl:text>G</xsl:text>
            </xsl:with-param>
            <xsl:with-param name="nr" select="@relnr"/>
            <xsl:with-param name="sym">
              <xsl:call-template name="abs1">
                <xsl:with-param name="k">
                  <xsl:text>G</xsl:text>
                </xsl:with-param>
                <xsl:with-param name="nr" select="@relnr"/>
              </xsl:call-template>
            </xsl:with-param>
          </xsl:call-template>
          <xsl:text>(# </xsl:text>
        </xsl:for-each>
        <xsl:for-each select="Constructor[@kind=&quot;L&quot;]/Fields/Field">
          <xsl:call-template name="abs">
            <xsl:with-param name="k">
              <xsl:text>U</xsl:text>
            </xsl:with-param>
            <xsl:with-param name="nr" select="@nr"/>
            <xsl:with-param name="sym">
              <xsl:call-template name="abs1">
                <xsl:with-param name="k">
                  <xsl:text>U</xsl:text>
                </xsl:with-param>
                <xsl:with-param name="nr" select="@nr"/>
              </xsl:call-template>
            </xsl:with-param>
          </xsl:call-template>
          <xsl:if test="not(position()=last())">
            <xsl:text>, </xsl:text>
          </xsl:if>
        </xsl:for-each>
        <xsl:text> #)</xsl:text>
        <xsl:element name="b">
          <xsl:text> -&gt; </xsl:text>
        </xsl:element>
        <xsl:apply-templates select="Constructor[@kind=&quot;G&quot;]/Typ"/>
        <xsl:text>;</xsl:text>
        <xsl:element name="br"/>
        <xsl:for-each select="Constructor[@kind=&quot;L&quot;]">
          <xsl:element name="a">
            <xsl:attribute name="NAME">
              <xsl:value-of select="concat(&quot;L&quot;,@nr)"/>
            </xsl:attribute>
            <xsl:element name="b">
              <xsl:text>struct </xsl:text>
            </xsl:element>
          </xsl:element>
          <xsl:call-template name="abs">
            <xsl:with-param name="k">
              <xsl:text>L</xsl:text>
            </xsl:with-param>
            <xsl:with-param name="nr" select="@relnr"/>
            <xsl:with-param name="sym">
              <xsl:call-template name="abs1">
                <xsl:with-param name="k">
                  <xsl:text>G</xsl:text>
                </xsl:with-param>
                <xsl:with-param name="nr" select="@relnr"/>
              </xsl:call-template>
            </xsl:with-param>
          </xsl:call-template>
          <xsl:text>( </xsl:text>
          <xsl:call-template name="arglist">
            <xsl:with-param name="separ">
              <xsl:text>,</xsl:text>
            </xsl:with-param>
            <xsl:with-param name="elems" select="ArgTypes/Typ"/>
          </xsl:call-template>
          <xsl:text>) </xsl:text>
          <xsl:element name="b">
            <xsl:text>-&gt; </xsl:text>
          </xsl:element>
          <xsl:text>( </xsl:text>
          <xsl:call-template name="list">
            <xsl:with-param name="separ">
              <xsl:text>, </xsl:text>
            </xsl:with-param>
            <xsl:with-param name="elems" select="Typ"/>
          </xsl:call-template>
          <xsl:text> );</xsl:text>
          <xsl:element name="br"/>
        </xsl:for-each>
        <xsl:for-each select="Constructor[@kind=&quot;U&quot;]">
          <xsl:element name="a">
            <xsl:attribute name="NAME">
              <xsl:value-of select="concat(&quot;U&quot;,@nr)"/>
            </xsl:attribute>
            <xsl:element name="b">
              <xsl:text>selector </xsl:text>
            </xsl:element>
          </xsl:element>
          <xsl:call-template name="abs">
            <xsl:with-param name="k">
              <xsl:text>U</xsl:text>
            </xsl:with-param>
            <xsl:with-param name="nr" select="@relnr"/>
            <xsl:with-param name="sym">
              <xsl:call-template name="abs1">
                <xsl:with-param name="k">
                  <xsl:text>U</xsl:text>
                </xsl:with-param>
                <xsl:with-param name="nr" select="@relnr"/>
              </xsl:call-template>
            </xsl:with-param>
          </xsl:call-template>
          <xsl:text>( </xsl:text>
          <xsl:call-template name="arglist">
            <xsl:with-param name="separ">
              <xsl:text>,</xsl:text>
            </xsl:with-param>
            <xsl:with-param name="elems" select="ArgTypes/Typ"/>
          </xsl:call-template>
          <xsl:text>) </xsl:text>
          <xsl:element name="b">
            <xsl:text>-&gt; </xsl:text>
          </xsl:element>
          <xsl:apply-templates select="Typ"/>
          <xsl:element name="br"/>
        </xsl:for-each>
        <xsl:for-each select="Constructor[@kind=&quot;V&quot;]">
          <xsl:element name="a">
            <xsl:attribute name="NAME">
              <xsl:value-of select="concat(&quot;V&quot;,@nr)"/>
            </xsl:attribute>
            <xsl:element name="b">
              <xsl:text>attr </xsl:text>
            </xsl:element>
          </xsl:element>
          <xsl:call-template name="abs">
            <xsl:with-param name="k">
              <xsl:text>V</xsl:text>
            </xsl:with-param>
            <xsl:with-param name="nr" select="@relnr"/>
            <xsl:with-param name="sym">
              <xsl:call-template name="abs1">
                <xsl:with-param name="k">
                  <xsl:text>V</xsl:text>
                </xsl:with-param>
                <xsl:with-param name="nr" select="@relnr"/>
              </xsl:call-template>
            </xsl:with-param>
          </xsl:call-template>
          <xsl:text>( </xsl:text>
          <xsl:call-template name="arglist">
            <xsl:with-param name="separ">
              <xsl:text>,</xsl:text>
            </xsl:with-param>
            <xsl:with-param name="elems" select="ArgTypes/Typ"/>
          </xsl:call-template>
          <xsl:text>)</xsl:text>
          <xsl:element name="br"/>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="@expandable=&quot;true&quot;">
            <xsl:element name="b">
              <xsl:text>expandable mode;</xsl:text>
            </xsl:element>
            <xsl:element name="br"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:if test="@redefinition=&quot;true&quot;">
              <xsl:element name="b">
                <xsl:text>redefine </xsl:text>
              </xsl:element>
            </xsl:if>
            <xsl:for-each select="Constructor">
              <xsl:element name="a">
                <xsl:attribute name="NAME">
                  <xsl:value-of select="concat(@kind,@nr)"/>
                </xsl:attribute>
                <xsl:element name="b">
                  <xsl:call-template name="mkind">
                    <xsl:with-param name="kind" select="@kind"/>
                  </xsl:call-template>
                </xsl:element>
                <xsl:text> </xsl:text>
              </xsl:element>
              <xsl:if test="../@redefinition=&quot;true&quot;">
                <xsl:call-template name="abs">
                  <xsl:with-param name="k" select="@kind"/>
                  <xsl:with-param name="nr" select="@redefnr"/>
                  <xsl:with-param name="sym">
                    <xsl:call-template name="abs1">
                      <xsl:with-param name="k" select="@kind"/>
                      <xsl:with-param name="nr" select="@redefnr"/>
                    </xsl:call-template>
                  </xsl:with-param>
                </xsl:call-template>
                <xsl:text> as </xsl:text>
              </xsl:if>
              <xsl:call-template name="abs">
                <xsl:with-param name="k" select="@kind"/>
                <xsl:with-param name="nr" select="@relnr"/>
                <xsl:with-param name="sym">
                  <xsl:call-template name="abs1">
                    <xsl:with-param name="k" select="@kind"/>
                    <xsl:with-param name="nr" select="@relnr"/>
                  </xsl:call-template>
                </xsl:with-param>
              </xsl:call-template>
              <xsl:text>( </xsl:text>
              <xsl:call-template name="arglist">
                <xsl:with-param name="separ">
                  <xsl:text>,</xsl:text>
                </xsl:with-param>
                <xsl:with-param name="elems" select="ArgTypes/Typ"/>
              </xsl:call-template>
              <xsl:text>)</xsl:text>
              <xsl:if test="(@kind = &apos;M&apos;) or (@kind = &apos;K&apos;)">
                <xsl:element name="b">
                  <xsl:text> -&gt; </xsl:text>
                </xsl:element>
                <xsl:apply-templates select="Typ"/>
              </xsl:if>
              <xsl:text>;</xsl:text>
              <xsl:element name="br"/>
            </xsl:for-each>
            <xsl:apply-templates select="*[not(name()=&apos;Constructor&apos;)]"/>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- ( elLet | elAssume | elGiven | AuxiliaryItem | -->
  <!-- elCanceled | elDefinition )*, elEndPosition -->
  <xsl:template match="DefinitionBlock">
    <xsl:element name="div">
      <xsl:element name="b">
        <xsl:text>definition</xsl:text>
      </xsl:element>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="*[not(name()=&apos;EndPosition&apos;)]"/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- ( elRCluster | elFCluster | elCCluster ), -->
  <!-- CorrectnessCondition*, elCorrectness? -->
  <xsl:template match="Registration">
    <xsl:apply-templates/>
  </xsl:template>

  <!-- ( elLet | AuxiliaryItem | elRegistration | elCanceled )+, elEndPosition -->
  <xsl:template match="RegistrationBlock">
    <xsl:element name="div">
      <xsl:element name="b">
        <xsl:text>registration</xsl:text>
      </xsl:element>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="*[not(name()=&apos;EndPosition&apos;)]"/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <xsl:template match="NotationBlock">
    <xsl:element name="div">
      <xsl:element name="b">
        <xsl:text>notation</xsl:text>
      </xsl:element>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="*[not(name()=&apos;EndPosition&apos;)]"/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- List utilities -->
  <xsl:template name="list">
    <xsl:param name="separ"/>
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:apply-templates select="."/>
      <xsl:if test="not(position()=last())">
        <xsl:value-of select="$separ"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <!-- List utility with additional arg -->
  <xsl:template name="ilist">
    <xsl:param name="separ"/>
    <xsl:param name="elems"/>
    <xsl:param name="i"/>
    <xsl:for-each select="$elems">
      <xsl:apply-templates select=".">
        <xsl:with-param name="i" select="$i"/>
      </xsl:apply-templates>
      <xsl:if test="not(position()=last())">
        <xsl:value-of select="$separ"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <!-- newlined list -->
  <xsl:template name="nlist">
    <xsl:param name="separ"/>
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:apply-templates select="."/>
      <xsl:if test="not(position()=last())">
        <xsl:element name="br"/>
        <xsl:value-of select="$separ"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="dlist">
    <xsl:param name="separ"/>
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:element name="div">
        <xsl:apply-templates select="."/>
        <xsl:if test="not(position()=last())">
          <xsl:value-of select="$separ"/>
        </xsl:if>
      </xsl:element>
    </xsl:for-each>
  </xsl:template>

  <!-- argument list -->
  <xsl:template name="arglist">
    <xsl:param name="separ"/>
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:call-template name="ploci">
        <xsl:with-param name="nr" select="position()"/>
      </xsl:call-template>
      <xsl:if test="not(position()=last())">
        <xsl:value-of select="$separ"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <!-- add numbers starting at #j+1 between #sep1 and #sep2 - now with constants -->
  <xsl:template name="jlist">
    <xsl:param name="j"/>
    <xsl:param name="sep1"/>
    <xsl:param name="sep2"/>
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:apply-templates select="."/>
      <xsl:if test="not(position()=last())">
        <xsl:value-of select="$sep1"/>
        <xsl:call-template name="pconst">
          <xsl:with-param name="nr" select="$j+position()"/>
        </xsl:call-template>
        <xsl:value-of select="$sep2"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <!-- from-to list of variables starting numbering at $f ending at $t -->
  <xsl:template name="ft_list">
    <xsl:param name="f"/>
    <xsl:param name="t"/>
    <xsl:param name="sep"/>
    <xsl:choose>
      <xsl:when test="$f = $t">
        <xsl:call-template name="pvar">
          <xsl:with-param name="nr" select="$f"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:if test="$f &lt; $t">
          <xsl:call-template name="pvar">
            <xsl:with-param name="nr" select="$f"/>
          </xsl:call-template>
          <xsl:value-of select="$sep"/>
          <xsl:call-template name="ft_list">
            <xsl:with-param name="f" select="$f+1"/>
            <xsl:with-param name="t" select="$t"/>
            <xsl:with-param name="sep" select="$sep"/>
          </xsl:call-template>
        </xsl:if>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- add the constructor href, $c tells if it is from current article -->
  <!-- #sym is optional Mizar symbol -->
  <xsl:template name="absref">
    <xsl:param name="elems"/>
    <xsl:param name="c"/>
    <xsl:param name="sym"/>
    <xsl:for-each select="$elems">
      <xsl:variable name="mk">
        <xsl:call-template name="mkind">
          <xsl:with-param name="kind" select="@kind"/>
        </xsl:call-template>
      </xsl:variable>
      <xsl:element name="a">
        <xsl:choose>
          <xsl:when test="($linking = &apos;q&apos;) or (($linking = &apos;m&apos;) and not($c))">
            <xsl:attribute name="href">
              <xsl:value-of select="concat($mmlq,@aid,&quot;:&quot;,$mk,&quot;.&quot;,@nr)"/>
            </xsl:attribute>
            <xsl:attribute name="title">
              <xsl:value-of select="concat(@aid,&quot;:&quot;,$mk,&quot;.&quot;,@nr)"/>
            </xsl:attribute>
          </xsl:when>
          <xsl:otherwise>
            <xsl:attribute name="href">
              <xsl:value-of select="concat(translate(@aid,$ucletters,$lcletters),
                       &quot;.xml#&quot;,@kind,@nr)"/>
            </xsl:attribute>
            <xsl:attribute name="title">
              <xsl:value-of select="concat(translate(@aid,$ucletters,$lcletters),
	                &quot;:&quot;,$mk,&quot;.&quot;,@nr)"/>
            </xsl:attribute>
            <xsl:if test="$c">
              <xsl:attribute name="target">
                <xsl:text>_self</xsl:text>
              </xsl:attribute>
            </xsl:if>
          </xsl:otherwise>
        </xsl:choose>
        <xsl:choose>
          <xsl:when test="$sym">
            <xsl:value-of select="$sym"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:choose>
              <xsl:when test="$relnames&gt;0">
                <xsl:value-of select="@kind"/>
                <xsl:value-of select="@relnr"/>
              </xsl:when>
              <xsl:otherwise>
                <xsl:value-of select="@kind"/>
                <xsl:value-of select="@nr"/>
                <xsl:text>_</xsl:text>
                <xsl:value-of select="@aid"/>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:element>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="abs">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:param name="sym"/>
    <xsl:choose>
      <xsl:when test="key($k,$nr)">
        <xsl:call-template name="absref">
          <xsl:with-param name="elems" select="key($k,$nr)"/>
          <xsl:with-param name="c">
            <xsl:text>1</xsl:text>
          </xsl:with-param>
          <xsl:with-param name="sym" select="$sym"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:for-each select="document($constrs,/)">
          <xsl:call-template name="absref">
            <xsl:with-param name="elems" select="key($k,$nr)"/>
            <xsl:with-param name="sym" select="$sym"/>
          </xsl:call-template>
        </xsl:for-each>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- return first symbol corresponding to constructor; -->
  <!-- if nothing found, just concat #k and #nr; #r says to look for -->
  <!-- right bracket instead of left or fail if the format is not bracket -->
  <xsl:template name="abs1">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:param name="r"/>
    <xsl:variable name="fnr">
      <xsl:call-template name="formt_nr">
        <xsl:with-param name="k" select="$k"/>
        <xsl:with-param name="nr" select="$nr"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:for-each select="document($formats,/)">
      <xsl:choose>
        <xsl:when test="not(key(&apos;F&apos;,$fnr))">
          <xsl:value-of select="concat($k,$nr)"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:for-each select="key(&apos;F&apos;,$fnr)">
            <xsl:variable name="snr" select="@symbolnr"/>
            <xsl:variable name="sk" select="@kind"/>
            <xsl:variable name="dkey" select="concat(&apos;D_&apos;,@kind)"/>
            <xsl:variable name="rsnr">
              <xsl:if test="$sk=&apos;K&apos;">
                <xsl:value-of select="@rightsymbolnr"/>
              </xsl:if>
            </xsl:variable>
            <xsl:if test="not($r=&apos;1&apos;) or ($sk=&apos;K&apos;)">
              <xsl:for-each select="document($vocs,/)">
                <xsl:choose>
                  <xsl:when test="key($dkey,$snr)">
                    <xsl:for-each select="key($dkey,$snr)">
                      <xsl:choose>
                        <xsl:when test="($sk=&apos;K&apos;) and ($r=&apos;1&apos;)">
                          <xsl:for-each select="key(&apos;D_L&apos;,$rsnr)">
                            <xsl:value-of select="@name"/>
                          </xsl:for-each>
                        </xsl:when>
                        <xsl:otherwise>
                          <xsl:value-of select="@name"/>
                        </xsl:otherwise>
                      </xsl:choose>
                    </xsl:for-each>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:choose>
                      <xsl:when test="($snr=&apos;1&apos;) and ($sk=&apos;M&apos;)">
                        <xsl:text>set</xsl:text>
                      </xsl:when>
                      <xsl:when test="($snr=&apos;1&apos;) and ($sk=&apos;R&apos;)">
                        <xsl:text>=</xsl:text>
                      </xsl:when>
                      <xsl:when test="($snr=&apos;1&apos;) and ($sk=&apos;K&apos;)">
                        <xsl:choose>
                          <xsl:when test="$r=&apos;1&apos;">
                            <xsl:text>]</xsl:text>
                          </xsl:when>
                          <xsl:otherwise>
                            <xsl:text>[</xsl:text>
                          </xsl:otherwise>
                        </xsl:choose>
                      </xsl:when>
                      <xsl:when test="($snr=&apos;2&apos;) and ($sk=&apos;K&apos;)">
                        <xsl:choose>
                          <xsl:when test="$r=&apos;1&apos;">
                            <xsl:text>}</xsl:text>
                          </xsl:when>
                          <xsl:otherwise>
                            <xsl:text>{</xsl:text>
                          </xsl:otherwise>
                        </xsl:choose>
                      </xsl:when>
                      <xsl:otherwise>
                        <xsl:value-of select="concat($k,$nr)"/>
                      </xsl:otherwise>
                    </xsl:choose>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:for-each>
            </xsl:if>
          </xsl:for-each>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="formt_nr">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:variable name="pkey" select="concat(&apos;P_&apos;,$k)"/>
    <xsl:choose>
      <xsl:when test="key($pkey,$nr)">
        <xsl:for-each select="key($pkey,$nr)[position()=1]">
          <xsl:value-of select="@formatnr"/>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <xsl:for-each select="document($patts,/)">
          <xsl:for-each select="key($pkey,$nr)[position()=1]">
            <xsl:value-of select="@formatnr"/>
          </xsl:for-each>
        </xsl:for-each>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- pretty printer - gets arguments, visibility info from pattern, -->
  <!-- format telling arities, the linked symbol and optionally right bracket -->
  <!-- parenth hints to put the whole expression in parentheses, but this -->
  <!-- is overrriden if the expression uses functor brackets -->
  <xsl:template name="pp">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:param name="args"/>
    <xsl:param name="parenth"/>
    <xsl:variable name="pkey" select="concat(&apos;P_&apos;,$k)"/>
    <xsl:choose>
      <xsl:when test="key($pkey,$nr)">
        <xsl:for-each select="key($pkey,$nr)[position()=1]">
          <xsl:call-template name="pp1">
            <xsl:with-param name="k" select="$k"/>
            <xsl:with-param name="nr" select="$nr"/>
            <xsl:with-param name="args" select="$args"/>
            <xsl:with-param name="vis" select="Visible/Int"/>
            <xsl:with-param name="fnr" select="@formatnr"/>
            <xsl:with-param name="parenth" select="$parenth"/>
          </xsl:call-template>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <xsl:for-each select="document($patts,/)">
          <xsl:for-each select="key($pkey,$nr)[position()=1]">
            <xsl:call-template name="pp1">
              <xsl:with-param name="k" select="$k"/>
              <xsl:with-param name="nr" select="$nr"/>
              <xsl:with-param name="args" select="$args"/>
              <xsl:with-param name="vis" select="Visible/Int"/>
              <xsl:with-param name="fnr" select="@formatnr"/>
              <xsl:with-param name="parenth" select="$parenth"/>
            </xsl:call-template>
          </xsl:for-each>
        </xsl:for-each>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="pp1">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:param name="args"/>
    <xsl:param name="vis"/>
    <xsl:param name="fnr"/>
    <xsl:param name="parenth"/>
    <xsl:variable name="la">
      <xsl:choose>
        <xsl:when test="($k=&apos;M&apos;) or ($k=&apos;G&apos;) or ($k=&apos;L&apos;)">
          <xsl:text>0</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:for-each select="document($formats,/)">
            <xsl:for-each select="key(&apos;F&apos;,$fnr)">
              <xsl:choose>
                <xsl:when test="@leftargnr">
                  <xsl:value-of select="@leftargnr"/>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:text>0</xsl:text>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:for-each>
          </xsl:for-each>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <!-- try if right bracket -->
    <xsl:variable name="rsym">
      <xsl:if test="($k=&apos;K&apos;) and ($la=&apos;0&apos;)">
        <xsl:call-template name="abs1">
          <xsl:with-param name="k" select="$k"/>
          <xsl:with-param name="nr" select="$nr"/>
          <xsl:with-param name="r">
            <xsl:text>1</xsl:text>
          </xsl:with-param>
        </xsl:call-template>
      </xsl:if>
    </xsl:variable>
    <xsl:variable name="np">
      <xsl:choose>
        <xsl:when test="not($args)">
          <xsl:text>0</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:choose>
            <xsl:when test="$parenth&gt;0">
              <xsl:value-of select="$parenth"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:choose>
                <xsl:when test="not($rsym=&apos;&apos;)">
                  <xsl:text>1</xsl:text>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:text>0</xsl:text>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="paren_color" select="$np mod $pcolors_nr"/>
    <!-- print spanned paranthesis or left bracket -->
    <xsl:choose>
      <xsl:when test="($np&gt;0)">
        <xsl:element name="span">
          <xsl:attribute name="class">
            <xsl:value-of select="concat(&quot;paren&quot;,$paren_color)"/>
          </xsl:attribute>
          <xsl:choose>
            <xsl:when test="$rsym=&apos;&apos;">
              <xsl:text>(</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:call-template name="abs">
                <xsl:with-param name="k" select="$k"/>
                <xsl:with-param name="nr" select="$nr"/>
                <xsl:with-param name="sym">
                  <xsl:call-template name="abs1">
                    <xsl:with-param name="k" select="$k"/>
                    <xsl:with-param name="nr" select="$nr"/>
                  </xsl:call-template>
                </xsl:with-param>
              </xsl:call-template>
            </xsl:otherwise>
          </xsl:choose>
          <xsl:element name="span">
            <xsl:attribute name="class">
              <xsl:text>default</xsl:text>
            </xsl:attribute>
            <!-- this is duplicated later - needed for Mozilla - bad escaping -->
            <xsl:for-each select="$vis">
              <xsl:if test="position() &lt;= $la">
                <xsl:variable name="x" select="@x"/>
                <xsl:apply-templates select="$args[position() = $x]">
                  <xsl:with-param name="p" select="$np"/>
                </xsl:apply-templates>
                <xsl:if test="position() &lt; $la">
                  <xsl:text>,</xsl:text>
                </xsl:if>
              </xsl:if>
            </xsl:for-each>
            <xsl:if test="$rsym=&apos;&apos;">
              <xsl:if test="not($parenth&gt;0) or ($la&gt;0)">
                <xsl:text> </xsl:text>
              </xsl:if>
              <xsl:call-template name="abs">
                <xsl:with-param name="k" select="$k"/>
                <xsl:with-param name="nr" select="$nr"/>
                <xsl:with-param name="sym">
                  <xsl:call-template name="abs1">
                    <xsl:with-param name="k" select="$k"/>
                    <xsl:with-param name="nr" select="$nr"/>
                  </xsl:call-template>
                </xsl:with-param>
              </xsl:call-template>
              <xsl:text> </xsl:text>
            </xsl:if>
            <xsl:for-each select="$vis">
              <xsl:if test="(position() = 1) and (($k=&apos;M&apos;) or ($k=&apos;L&apos;))">
                <xsl:text>of </xsl:text>
              </xsl:if>
              <xsl:if test="position() &gt; $la">
                <xsl:variable name="x" select="@x"/>
                <xsl:apply-templates select="$args[position()  = $x]">
                  <xsl:with-param name="p" select="$np"/>
                </xsl:apply-templates>
                <xsl:if test="position() &lt; last()">
                  <xsl:text>,</xsl:text>
                </xsl:if>
              </xsl:if>
            </xsl:for-each>
          </xsl:element>
          <xsl:choose>
            <xsl:when test="$rsym=&apos;&apos;">
              <xsl:text>)</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:call-template name="abs">
                <xsl:with-param name="k" select="$k"/>
                <xsl:with-param name="nr" select="$nr"/>
                <xsl:with-param name="sym" select="$rsym"/>
              </xsl:call-template>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:for-each select="$vis">
          <xsl:if test="position() &lt;= $la">
            <xsl:variable name="x" select="@x"/>
            <xsl:apply-templates select="$args[position() = $x]">
              <xsl:with-param name="p" select="$np"/>
            </xsl:apply-templates>
            <xsl:if test="position() &lt; $la">
              <xsl:text>,</xsl:text>
            </xsl:if>
          </xsl:if>
        </xsl:for-each>
        <xsl:if test="$rsym=&apos;&apos;">
          <xsl:if test="not($parenth&gt;0) or ($la&gt;0)">
            <xsl:text> </xsl:text>
          </xsl:if>
          <xsl:call-template name="abs">
            <xsl:with-param name="k" select="$k"/>
            <xsl:with-param name="nr" select="$nr"/>
            <xsl:with-param name="sym">
              <xsl:call-template name="abs1">
                <xsl:with-param name="k" select="$k"/>
                <xsl:with-param name="nr" select="$nr"/>
              </xsl:call-template>
            </xsl:with-param>
          </xsl:call-template>
          <xsl:text> </xsl:text>
        </xsl:if>
        <xsl:for-each select="$vis">
          <xsl:if test="(position() = 1) and (($k=&apos;M&apos;) or ($k=&apos;L&apos;))">
            <xsl:text>of </xsl:text>
          </xsl:if>
          <xsl:if test="position() &gt; $la">
            <xsl:variable name="x" select="@x"/>
            <xsl:apply-templates select="$args[position()  = $x]">
              <xsl:with-param name="p" select="$np"/>
            </xsl:apply-templates>
            <xsl:if test="position() &lt; last()">
              <xsl:text>,</xsl:text>
            </xsl:if>
          </xsl:if>
        </xsl:for-each>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- apply[.]; if [not(position()=last())] { $sep1; `$j+position()`; $sep2; } }} -->
  <!-- pretty print variables and labels -->
  <xsl:template name="pvar">
    <xsl:param name="nr"/>
    <xsl:element name="font">
      <xsl:attribute name="color">
        <xsl:value-of select="$varcolor"/>
      </xsl:attribute>
      <xsl:text>b</xsl:text>
      <xsl:element name="sub">
        <xsl:value-of select="$nr"/>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <xsl:template name="pconst">
    <xsl:param name="nr"/>
    <xsl:element name="font">
      <xsl:attribute name="color">
        <xsl:value-of select="$constcolor"/>
      </xsl:attribute>
      <xsl:text>c</xsl:text>
      <xsl:element name="sub">
        <xsl:value-of select="$nr"/>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <xsl:template name="ploci">
    <xsl:param name="nr"/>
    <xsl:element name="font">
      <xsl:attribute name="color">
        <xsl:value-of select="$locicolor"/>
      </xsl:attribute>
      <xsl:text>a</xsl:text>
      <xsl:element name="sub">
        <xsl:value-of select="$nr"/>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <xsl:template name="plab">
    <xsl:param name="nr"/>
    <xsl:element name="i">
      <xsl:element name="font">
        <xsl:attribute name="color">
          <xsl:value-of select="$labcolor"/>
        </xsl:attribute>
        <xsl:text>E</xsl:text>
        <xsl:value-of select="@nr"/>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- theorem, definition and scheme references -->
  <!-- add the reference's href, $c tells if it is from current article -->
  <xsl:template name="mkref">
    <xsl:param name="aid"/>
    <xsl:param name="nr"/>
    <xsl:param name="k"/>
    <xsl:param name="c"/>
    <xsl:variable name="mk">
      <xsl:call-template name="refkind">
        <xsl:with-param name="kind" select="$k"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:element name="a">
      <xsl:attribute name="class">
        <xsl:text>ref</xsl:text>
      </xsl:attribute>
      <xsl:choose>
        <xsl:when test="($linking = &apos;q&apos;) or (($linking = &apos;m&apos;) and not($c))">
          <xsl:attribute name="href">
            <xsl:value-of select="concat($mmlq,$aid,&quot;:&quot;,$mk,&quot;.&quot;,$nr)"/>
          </xsl:attribute>
          <xsl:attribute name="title">
            <xsl:value-of select="concat($aid,&quot;:&quot;,$mk,&quot;.&quot;,$nr)"/>
          </xsl:attribute>
        </xsl:when>
        <xsl:otherwise>
          <xsl:attribute name="href">
            <xsl:value-of select="concat(translate($aid,$ucletters,$lcletters),
                       &quot;.xml#&quot;,$k,$nr)"/>
          </xsl:attribute>
          <xsl:attribute name="title">
            <xsl:value-of select="concat(translate($aid,$ucletters,$lcletters),
                        &quot;:&quot;,$mk,&quot;.&quot;,$nr)"/>
          </xsl:attribute>
          <xsl:if test="$c">
            <xsl:attribute name="target">
              <xsl:text>_self</xsl:text>
            </xsl:attribute>
          </xsl:if>
        </xsl:otherwise>
      </xsl:choose>
      <xsl:value-of select="$aid"/>
      <xsl:text>:</xsl:text>
      <xsl:value-of select="$mk"/>
      <xsl:text> </xsl:text>
      <xsl:value-of select="$nr"/>
    </xsl:element>
  </xsl:template>

  <xsl:template name="getschref">
    <xsl:param name="anr"/>
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$anr&gt;0">
        <xsl:for-each select="document($schms,/)">
          <xsl:for-each select="key(&apos;S&apos;,concat($anr,&apos;:&apos;,$nr))">
            <xsl:call-template name="mkref">
              <xsl:with-param name="aid" select="@aid"/>
              <xsl:with-param name="nr" select="$nr"/>
              <xsl:with-param name="k">
                <xsl:text>S</xsl:text>
              </xsl:with-param>
            </xsl:call-template>
          </xsl:for-each>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="mkref">
          <xsl:with-param name="aid" select="$aname"/>
          <xsl:with-param name="nr" select="$nr"/>
          <xsl:with-param name="k">
            <xsl:text>S</xsl:text>
          </xsl:with-param>
          <xsl:with-param name="c">
            <xsl:text>1</xsl:text>
          </xsl:with-param>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="getref">
    <xsl:param name="k"/>
    <xsl:param name="anr"/>
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$anr&gt;0">
        <xsl:for-each select="document($thms,/)">
          <xsl:for-each select="key($k,concat($anr,&apos;:&apos;,$nr))">
            <xsl:call-template name="mkref">
              <xsl:with-param name="aid" select="@aid"/>
              <xsl:with-param name="nr" select="$nr"/>
              <xsl:with-param name="k" select="$k"/>
            </xsl:call-template>
          </xsl:for-each>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="mkref">
          <xsl:with-param name="aid" select="$aname"/>
          <xsl:with-param name="nr" select="$nr"/>
          <xsl:with-param name="k" select="$k"/>
          <xsl:with-param name="c">
            <xsl:text>1</xsl:text>
          </xsl:with-param>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- translate constructor kinds to their mizar/mmlquery names -->
  <xsl:template name="mkind">
    <xsl:param name="kind"/>
    <xsl:choose>
      <xsl:when test="$kind = &apos;M&apos;">
        <xsl:text>mode</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;V&apos;">
        <xsl:text>attr</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;R&apos;">
        <xsl:text>pred</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;K&apos;">
        <xsl:text>func</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;G&apos;">
        <xsl:text>aggr</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;L&apos;">
        <xsl:text>struct</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;U&apos;">
        <xsl:text>sel</xsl:text>
      </xsl:when>
    </xsl:choose>
  </xsl:template>

  <!-- translate reference kinds to their mizar/mmlquery names -->
  <xsl:template name="refkind">
    <xsl:param name="kind"/>
    <xsl:choose>
      <xsl:when test="$kind = &apos;T&apos;">
        <xsl:text>th</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;D&apos;">
        <xsl:text>def</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;S&apos;">
        <xsl:text>sch</xsl:text>
      </xsl:when>
    </xsl:choose>
  </xsl:template>

  <!-- separate top-level items by additional newline -->
  <xsl:template match="Article">
    <xsl:text>:: </xsl:text>
    <xsl:value-of select="@aid"/>
    <xsl:text>  semantic presentation</xsl:text>
    <xsl:element name="br"/>
    <xsl:element name="br"/>
    <xsl:for-each select="*">
      <xsl:apply-templates select="."/>
      <xsl:if test="(not(name()=&apos;Definiens&apos;)) and (not(name()=&apos;Reservation&apos;)) 
          and (not(name()=&apos;Pattern&apos;))">
        <xsl:element name="br"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <!-- processing of imported documents -->
  <xsl:template match="Theorem">
    <xsl:element name="b">
      <xsl:text>theorem </xsl:text>
    </xsl:element>
    <xsl:call-template name="mkref">
      <xsl:with-param name="aid" select="@aid"/>
      <xsl:with-param name="nr" select="@nr"/>
      <xsl:with-param name="k" select="@kind"/>
    </xsl:call-template>
    <xsl:element name="br"/>
    <xsl:apply-templates/>
    <xsl:element name="br"/>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="Constructor">
    <xsl:element name="b">
      <xsl:text>constructor </xsl:text>
    </xsl:element>
    <xsl:call-template name="absref">
      <xsl:with-param name="elems" select="key(@kind,@relnr)"/>
    </xsl:call-template>
    <xsl:element name="br"/>
    <xsl:call-template name="absref">
      <xsl:with-param name="elems" select="key(@kind,@relnr)"/>
    </xsl:call-template>
    <xsl:text>( </xsl:text>
    <xsl:call-template name="arglist">
      <xsl:with-param name="separ">
        <xsl:text>,</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="ArgTypes/Typ"/>
    </xsl:call-template>
    <xsl:text>)</xsl:text>
    <xsl:if test="(@kind = &apos;M&apos;) or (@kind = &apos;K&apos;) or (@kind= &apos;G&apos;) 
        or (@kind= &apos;U&apos;) or (@kind= &apos;L&apos;)">
      <xsl:element name="b">
        <xsl:text> -&gt; </xsl:text>
      </xsl:element>
      <xsl:call-template name="list">
        <xsl:with-param name="separ">
          <xsl:text>,</xsl:text>
        </xsl:with-param>
        <xsl:with-param name="elems" select="Typ"/>
      </xsl:call-template>
    </xsl:if>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
    <xsl:element name="br"/>
  </xsl:template>

  <!-- ignore Patterns now -->
  <xsl:template match="Pattern"/>

  <!-- Default -->
  <xsl:template match="/">
    <xsl:element name="html">
      <!-- output the css defaults for div and p (for indenting) -->
      <xsl:element name="style">
        <xsl:attribute name="type">
          <xsl:text>text/css</xsl:text>
        </xsl:attribute>
        <xsl:text>
div { padding: 0 0 0 0; margin: 0 0 0 0; } 
div.add { padding-left: 3mm; padding-bottom: 0mm;  margin: 0 0 0 0; } 
p { margin: 0 0 0 0; } 
a {text-decoration:none} a:hover { color: red; } 
a.ref:link { color:green; } 
a.ref:hover { color: red; } 
span.paren1:hover { color : inherit; background-color : #BAFFFF; } 
span.paren2:hover { color : inherit; background-color : #FFCACA; }
span.paren3:hover { color : inherit; background-color : #FFFFBA; }
span.paren4:hover { color : inherit; background-color : #CACAFF; }
span.paren5:hover { color : inherit; background-color : #CAFFCA; }
span.paren0:hover { color : inherit; background-color : #FFBAFF; }
.default { background-color: white; color: black; } 
.default:hover { background-color: white; color: black; }
</xsl:text>
      </xsl:element>
      <xsl:element name="head">
        <xsl:element name="base">
          <xsl:attribute name="target">
            <xsl:text>mmlquery</xsl:text>
          </xsl:attribute>
        </xsl:element>
      </xsl:element>
      <xsl:element name="body">
        <!-- first read the keys for imported stuff -->
        <!-- apply[document($constrs,/)/Constructors/Constructor]; -->
        <!-- apply[document($thms,/)/Theorems/Theorem]; -->
        <!-- apply[document($schms,/)/Schemes/Scheme]; -->
        <!-- then process the whole document -->
        <xsl:apply-templates/>
      </xsl:element>
    </xsl:element>
  </xsl:template>
</xsl:stylesheet>
