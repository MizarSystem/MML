<?xml version='1.0' encoding='UTF-8'?>

<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
  <!-- XSLTXT (https://xsltxt.dev.java.net/) stylesheet taking -->
  <!-- XML terms, formulas and types to less verbose format. -->
  <!-- To produce standard XSLT from this do e.g.: -->
  <!-- java -jar xsltxt.jar toXSL miz.xsltxt >miz.xsl -->
  <!-- Then e.g.: xalan -XSL miz.xsl <ordinal2.pre >ordinal2.pre1 -->
  <!-- TODO: number B vars in fraenkel -->
  <!-- handle F and H parenthesis as K parenthesis -->
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
  <!-- The following are user-customizable -->
  <!-- mmlquery address -->
  <xsl:param name="mmlq">
    <xsl:text>http://merak.pb.bialystok.pl/mmlquery/fillin.php?entry=</xsl:text>
  </xsl:param>
  <!-- #mmlq= {"";} -->
  <!-- linking methods: -->
  <!-- "q" - query, everything is linked to mmlquery -->
  <!-- "s" - self, everything is linked to these xml files -->
  <!-- "m" - mizaring, current article's constructs are linked to self, -->
  <!-- the rest is linked to mmlquery -->
  <xsl:param name="linking">
    <xsl:text>s</xsl:text>
  </xsl:param>
  <!-- extension for linking - either xml or html -->
  <xsl:param name="ext">
    <xsl:text>html</xsl:text>
  </xsl:param>
  <!-- put titles to links or not -->
  <xsl:param name="titles">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <!-- coloured output or not -->
  <xsl:param name="colored">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <!-- tells whether relative or absolute names are shown -->
  <xsl:param name="relnames">
    <xsl:text>1</xsl:text>
  </xsl:param>
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
  <xsl:key name="DF" match="Definiens" use="@relnr"/>
  <!-- patterns are slightly tricky, since a predicate pattern -->
  <!-- may be linked to an attribute constructor; hence the -->
  <!-- indexing is done according to @constrkind and not @kind -->
  <!-- TODO: the attribute<->predicate change should propagate to usage -->
  <!-- of "is" -->
  <!-- Expandable modes have all @constrkind='M' and @constrnr=0, -->
  <!-- they are indexed separately only on their @relnr (@pid) -->
  <xsl:key name="P_M" match="Pattern[(@constrkind=&apos;M&apos;) and (@constrnr&gt;0)]" use="@constrnr"/>
  <xsl:key name="P_L" match="Pattern[@constrkind=&apos;L&apos;]" use="@constrnr"/>
  <xsl:key name="P_V" match="Pattern[@constrkind=&apos;V&apos;]" use="@constrnr"/>
  <xsl:key name="P_R" match="Pattern[@constrkind=&apos;R&apos;]" use="@constrnr"/>
  <xsl:key name="P_K" match="Pattern[@constrkind=&apos;K&apos;]" use="@constrnr"/>
  <xsl:key name="P_U" match="Pattern[@constrkind=&apos;U&apos;]" use="@constrnr"/>
  <xsl:key name="P_G" match="Pattern[@constrkind=&apos;G&apos;]" use="@constrnr"/>
  <xsl:key name="EXP" match="Pattern[(@constrkind=&apos;M&apos;) and (@constrnr=0)]" use="@relnr"/>
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
  <!-- this needs to be set to 1 for processing MML files -->
  <xsl:param name="mml">
    <xsl:choose>
      <xsl:when test="/Article">
        <xsl:text>0</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>1</xsl:text>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:param>
  <!-- nr. of clusters in Typ -->
  <!-- this is set to 1 for processing MML files -->
  <xsl:param name="cluster_nr">
    <xsl:choose>
      <xsl:when test="$mml = &quot;0&quot;">
        <xsl:text>2</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>1</xsl:text>
      </xsl:otherwise>
    </xsl:choose>
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
  <!-- .dfs file with imported definientia -->
  <xsl:param name="dfs">
    <xsl:value-of select="concat($anamelc, &apos;.dfs&apos;)"/>
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
  <xsl:param name="schpcolor">
    <xsl:text>Maroon</xsl:text>
  </xsl:param>
  <xsl:param name="schfcolor">
    <xsl:text>Maroon</xsl:text>
  </xsl:param>
  <xsl:param name="ppcolor">
    <xsl:text>Maroon</xsl:text>
  </xsl:param>
  <xsl:param name="pfcolor">
    <xsl:text>Maroon</xsl:text>
  </xsl:param>
  <xsl:param name="labcolor">
    <xsl:text>Green</xsl:text>
  </xsl:param>
  <xsl:param name="commentcolor">
    <xsl:text>Red</xsl:text>
  </xsl:param>
  <!-- number of parenthesis colors (see the stylesheet in the bottom) -->
  <xsl:param name="pcolors_nr">
    <xsl:text>6</xsl:text>
  </xsl:param>
  <!-- top level element instead of top-level document, which is hard to -->
  <!-- know -->
  <xsl:param name="top" select="/"/>

  <!-- relative nr of the first expandable mode -->
  <!-- #first_exp = { `//Pattern[(@constrkind='M') and (@constrnr=0)][1]/@relnr`; } -->
  <!-- Formulas -->
  <!-- #i is nr of the bound variable, 1 by default -->
  <!-- #k is start of the sequence of vars with the same type, $i by default -->
  <!-- we now output only one typing for such sequences -->
  <!-- #ex tells that we should print it as existential statement, -->
  <!-- i.e. also omitting the first descending Not (the caller -->
  <!-- should guarantee that there _is_ a Not after the block of For-s) -->
  <!-- #pr tells to put the formula in paranthesis -->
  <xsl:template match="For">
    <xsl:param name="i"/>
    <xsl:param name="k"/>
    <xsl:param name="ex"/>
    <xsl:param name="pr"/>
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
    <xsl:variable name="eq1">
      <xsl:choose>
        <xsl:when test="($nm = &quot;For&quot;) and (*[1]/@nr = *[2]/*[1]/@nr)">
          <xsl:call-template name="are_equal">
            <xsl:with-param name="el1" select="*[1]"/>
            <xsl:with-param name="el2" select="*[2]/*[1]"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:choose>
      <xsl:when test="$eq1=&quot;1&quot;">
        <xsl:apply-templates select="*[2]">
          <xsl:with-param name="i" select="$j+1"/>
          <xsl:with-param name="k" select="$l"/>
          <xsl:with-param name="ex" select="$ex"/>
          <xsl:with-param name="pr" select="$pr"/>
        </xsl:apply-templates>
      </xsl:when>
      <xsl:otherwise>
        <xsl:if test="$pr">
          <xsl:text>( </xsl:text>
        </xsl:if>
        <xsl:choose>
          <xsl:when test="$ex=&quot;1&quot;">
            <xsl:text>ex </xsl:text>
            <xsl:call-template name="ft_list">
              <xsl:with-param name="f" select="$l"/>
              <xsl:with-param name="t" select="$j"/>
              <xsl:with-param name="sep">
                <xsl:text>, </xsl:text>
              </xsl:with-param>
            </xsl:call-template>
            <xsl:text> being</xsl:text>
            <xsl:apply-templates select="*[1]"/>
            <xsl:choose>
              <xsl:when test="$nm = &quot;For&quot;">
                <xsl:apply-templates select="*[2]">
                  <xsl:with-param name="i" select="$j+1"/>
                  <xsl:with-param name="ex" select="$ex"/>
                </xsl:apply-templates>
              </xsl:when>
              <xsl:otherwise>
                <xsl:text> st </xsl:text>
                <xsl:if test="not(name(Not/*[1]) = &quot;Pred&quot;)">
                  <xsl:element name="br"/>
                </xsl:if>
                <xsl:apply-templates select="Not/*[1]">
                  <xsl:with-param name="i" select="$j+1"/>
                </xsl:apply-templates>
              </xsl:otherwise>
            </xsl:choose>
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
        <xsl:if test="$pr">
          <xsl:text> )</xsl:text>
        </xsl:if>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- tpl [And/For] { <div {"for B being"; apply[*[1]]; -->
  <!-- " holds "; <div { @class="add";  apply[*[2]]; } } } -->
  <!-- return 1 if this is a Not-ended sequence of For-s -->
  <xsl:template name="check_for_not">
    <xsl:param name="el"/>
    <xsl:choose>
      <xsl:when test="name($el)=&quot;Not&quot;">
        <xsl:text>1</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="name($el)=&quot;For&quot;">
            <xsl:call-template name="check_for_not">
              <xsl:with-param name="el" select="$el/*[2]"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text>0</xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="Not">
    <xsl:param name="i"/>
    <xsl:param name="pr"/>
    <xsl:variable name="fnb">
      <xsl:choose>
        <xsl:when test="For">
          <xsl:call-template name="check_for_not">
            <xsl:with-param name="el" select="*[1]/*[2]"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:choose>
      <xsl:when test="$fnb=&quot;1&quot;">
        <xsl:apply-templates select="*[1]">
          <xsl:with-param name="i" select="$i"/>
          <xsl:with-param name="ex">
            <xsl:text>1</xsl:text>
          </xsl:with-param>
        </xsl:apply-templates>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="Pred[(@kind=&apos;V&apos;) or (@kind=&apos;R&apos;)]">
            <xsl:apply-templates select="*[1]">
              <xsl:with-param name="i" select="$i"/>
              <xsl:with-param name="not">
                <xsl:text>1</xsl:text>
              </xsl:with-param>
            </xsl:apply-templates>
          </xsl:when>
          <xsl:otherwise>
            <xsl:variable name="i1">
              <xsl:call-template name="is_impl">
                <xsl:with-param name="el" select="."/>
              </xsl:call-template>
            </xsl:variable>
            <xsl:choose>
              <xsl:when test="$i1=&quot;1&quot;">
                <xsl:text>( </xsl:text>
                <xsl:apply-templates select="*[1]/*[1]">
                  <xsl:with-param name="i" select="$i"/>
                  <xsl:with-param name="pr">
                    <xsl:text>1</xsl:text>
                  </xsl:with-param>
                </xsl:apply-templates>
                <xsl:text> implies </xsl:text>
                <xsl:apply-templates select="*[1]/*[2]/*[1]">
                  <xsl:with-param name="i" select="$i"/>
                </xsl:apply-templates>
                <xsl:text> )</xsl:text>
              </xsl:when>
              <xsl:otherwise>
                <xsl:variable name="i2">
                  <xsl:call-template name="is_or">
                    <xsl:with-param name="el" select="."/>
                  </xsl:call-template>
                </xsl:variable>
                <xsl:choose>
                  <xsl:when test="$i2=&quot;1&quot;">
                    <xsl:text>( </xsl:text>
                    <xsl:apply-templates select="*[1]/*[1]/*[1]">
                      <xsl:with-param name="i" select="$i"/>
                      <xsl:with-param name="pr">
                        <xsl:text>1</xsl:text>
                      </xsl:with-param>
                    </xsl:apply-templates>
                    <xsl:text> or </xsl:text>
                    <xsl:apply-templates select="*[1]/*[2]/*[1]">
                      <xsl:with-param name="i" select="$i"/>
                    </xsl:apply-templates>
                    <xsl:text> )</xsl:text>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:variable name="i3">
                      <xsl:call-template name="is_impl1">
                        <xsl:with-param name="el" select="."/>
                      </xsl:call-template>
                    </xsl:variable>
                    <xsl:choose>
                      <xsl:when test="$i3=&quot;1&quot;">
                        <xsl:text>( ( </xsl:text>
                        <xsl:call-template name="ilist">
                          <xsl:with-param name="separ">
                            <xsl:text> &amp; </xsl:text>
                          </xsl:with-param>
                          <xsl:with-param name="elems" select="*[1]/*[not(name()=&quot;Not&quot;)]"/>
                          <xsl:with-param name="i" select="$i"/>
                          <xsl:with-param name="pr">
                            <xsl:text>1</xsl:text>
                          </xsl:with-param>
                        </xsl:call-template>
                        <xsl:text> )</xsl:text>
                        <xsl:text> implies </xsl:text>
                        <xsl:text>( </xsl:text>
                        <xsl:call-template name="ilist">
                          <xsl:with-param name="separ">
                            <xsl:text> or </xsl:text>
                          </xsl:with-param>
                          <xsl:with-param name="elems" select="*[1]/Not/*[1]"/>
                          <xsl:with-param name="i" select="$i"/>
                          <xsl:with-param name="pr">
                            <xsl:text>1</xsl:text>
                          </xsl:with-param>
                        </xsl:call-template>
                        <xsl:text> ) )</xsl:text>
                      </xsl:when>
                      <xsl:otherwise>
                        <xsl:text>not </xsl:text>
                        <xsl:apply-templates select="*[1]">
                          <xsl:with-param name="i" select="$i"/>
                        </xsl:apply-templates>
                      </xsl:otherwise>
                    </xsl:choose>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  <!-- tpl [And/Not] { if [For] { <div { "not "; apply[*[1]]; } } -->
  <!-- else { "not "; apply[*[1]]; } } -->
  <xsl:param name="pid_Ex">
    <xsl:text>-1</xsl:text>
  </xsl:param>
  <!-- usually NegFrmPtr -->
  <xsl:param name="pid_Ex_Univ">
    <xsl:text>-2</xsl:text>
  </xsl:param>
  <!-- usually UnivFrmPtr -->
  <xsl:param name="pid_Ex_InnerNot">
    <xsl:text>-3</xsl:text>
  </xsl:param>
  <!-- usually NegFrmPtr -->
  <xsl:param name="pid_Impl">
    <xsl:text>-4</xsl:text>
  </xsl:param>
  <!-- usually NegFrmPtr -->
  <xsl:param name="pid_Impl_And">
    <xsl:text>-5</xsl:text>
  </xsl:param>
  <!-- usually ConjFrmPtr -->
  <xsl:param name="pid_Impl_RightNot">
    <xsl:text>-6</xsl:text>
  </xsl:param>
  <!-- usually NegFrmPtr -->
  <xsl:param name="pid_Iff">
    <xsl:text>-7</xsl:text>
  </xsl:param>
  <!-- usually ConjFrmPtr -->
  <xsl:param name="pid_Or">
    <xsl:text>-8</xsl:text>
  </xsl:param>
  <!-- usually NegFrmPtr -->
  <xsl:param name="pid_Or_And">
    <xsl:text>-9</xsl:text>
  </xsl:param>
  <!-- usually ConjFrmPtr -->
  <xsl:param name="pid_Or_LeftNot">
    <xsl:text>-10</xsl:text>
  </xsl:param>
  <!-- usually NegFrmPtr -->
  <xsl:param name="pid_Or_RightNot">
    <xsl:text>-11</xsl:text>
  </xsl:param>

  <!-- usually NegFrmPtr -->
  <xsl:template name="is_or">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="(@pid=$pid_Or) 
        and (*[1][@pid=$pid_Or_And]) and (count(*[1]/*)=2)
	and (*[1]/*[1][@pid=$pid_Or_LeftNot])
	and (*[1]/*[2][@pid=$pid_Or_RightNot])">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="is_impl">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="(@pid=$pid_Impl) 
        and (*[1][@pid=$pid_Impl_And]) and (count(*[1]/*)=2)
	and (*[1]/*[2][@pid=$pid_Impl_RightNot])">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="is_impl1">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="(@pid=$pid_Impl) 
        and (*[1][@pid=$pid_Impl_And]) and (count(*[1]/*)&gt;2)
	and (*[1]/*[@pid=$pid_Impl_RightNot])">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="is_impl2">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="(@pid=$pid_Impl) 
        and (*[1][@pid=$pid_Impl_And]) and (count(*[1]/*)&gt;=2)
	and (*[1]/*[@pid=$pid_Impl_RightNot])">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="is_equiv">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:variable name="e1">
        <xsl:choose>
          <xsl:when test="(@pid=$pid_Iff) and (count(*)=2)">
            <xsl:variable name="i1">
              <xsl:call-template name="is_impl">
                <xsl:with-param name="el" select="$el/*[1]"/>
              </xsl:call-template>
            </xsl:variable>
            <xsl:choose>
              <xsl:when test="$i1=&quot;1&quot;">
                <xsl:call-template name="is_impl">
                  <xsl:with-param name="el" select="*[2]"/>
                </xsl:call-template>
              </xsl:when>
              <xsl:otherwise>
                <xsl:text>0</xsl:text>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text>0</xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:variable>
      <xsl:choose>
        <xsl:when test="$e1=&quot;1&quot;">
          <xsl:variable name="res1">
            <xsl:call-template name="are_equal">
              <xsl:with-param name="el1" select="*[1]/*[1]/*[1]"/>
              <xsl:with-param name="el2" select="*[2]/*[1]/*[2]/*[1]"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:variable name="res2">
            <xsl:call-template name="are_equal">
              <xsl:with-param name="el1" select="*[2]/*[1]/*[1]"/>
              <xsl:with-param name="el2" select="*[1]/*[1]/*[2]/*[1]"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:choose>
            <xsl:when test="($res1=&quot;1&quot;) and ($res2=&quot;1&quot;)">
              <xsl:text>1</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>0</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$e1"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <!-- recursive equality on subnodes and attributes -->
  <xsl:template name="are_equal">
    <xsl:param name="el1"/>
    <xsl:param name="el2"/>
    <xsl:choose>
      <xsl:when test=" not(name($el1)=name($el2)) or not(count($el1/*)=count($el2/*))
	or not(count($el1/@*)=count($el2/@*))">
        <xsl:text>0</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:variable name="s1">
          <xsl:for-each select="$el1/@*">
            <xsl:value-of select="string()"/>
          </xsl:for-each>
        </xsl:variable>
        <xsl:variable name="s2">
          <xsl:for-each select="$el2/@*">
            <xsl:value-of select="string()"/>
          </xsl:for-each>
        </xsl:variable>
        <xsl:choose>
          <xsl:when test="not($s1=$s2)">
            <xsl:text>0</xsl:text>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="are_equal_many">
              <xsl:with-param name="els1" select="$el1/*"/>
              <xsl:with-param name="els2" select="$el2/*"/>
              <xsl:with-param name="nr" select="count($el1/*)"/>
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="are_equal_many">
    <xsl:param name="els1"/>
    <xsl:param name="els2"/>
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$nr &gt; 0">
        <xsl:variable name="el1" select="$els1[position()=$nr]"/>
        <xsl:variable name="el2" select="$els2[position()=$nr]"/>
        <xsl:variable name="res1">
          <xsl:call-template name="are_equal">
            <xsl:with-param name="el1" select="$el1"/>
            <xsl:with-param name="el2" select="$el2"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:choose>
          <xsl:when test="$res1=&quot;1&quot;">
            <xsl:call-template name="are_equal_many">
              <xsl:with-param name="els1" select="$els1"/>
              <xsl:with-param name="els2" select="$els2"/>
              <xsl:with-param name="nr" select="$nr - 1"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text>0</xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>1</xsl:text>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="And">
    <xsl:param name="i"/>
    <xsl:param name="pr"/>
    <xsl:variable name="e1">
      <xsl:call-template name="is_equiv">
        <xsl:with-param name="el" select="."/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:choose>
      <xsl:when test="$e1=&quot;1&quot;">
        <xsl:text>( </xsl:text>
        <xsl:apply-templates select="*[1]/*[1]/*[1]">
          <xsl:with-param name="i" select="$i"/>
          <xsl:with-param name="pr">
            <xsl:text>1</xsl:text>
          </xsl:with-param>
        </xsl:apply-templates>
        <xsl:text> iff </xsl:text>
        <xsl:apply-templates select="*[1]/*[1]/*[2]/*[1]">
          <xsl:with-param name="i" select="$i"/>
        </xsl:apply-templates>
        <xsl:text> )</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <!-- a bit risky -->
        <xsl:choose>
          <xsl:when test="(@pid=$pid_Iff) and (count(*)=2)">
            <xsl:variable name="i1">
              <xsl:call-template name="is_impl">
                <xsl:with-param name="el" select="*[1]"/>
              </xsl:call-template>
            </xsl:variable>
            <xsl:choose>
              <xsl:when test="$i1=&quot;1&quot;">
                <xsl:text>( </xsl:text>
                <xsl:apply-templates select="*[1]/*[1]/*[1]">
                  <xsl:with-param name="i" select="$i"/>
                  <xsl:with-param name="pr">
                    <xsl:text>1</xsl:text>
                  </xsl:with-param>
                </xsl:apply-templates>
                <xsl:text> iff </xsl:text>
                <xsl:apply-templates select="*[1]/*[1]/*[2]/*[1]">
                  <xsl:with-param name="i" select="$i"/>
                </xsl:apply-templates>
                <xsl:text> )</xsl:text>
              </xsl:when>
              <xsl:otherwise>
                <xsl:variable name="i2">
                  <xsl:call-template name="is_impl">
                    <xsl:with-param name="el" select="*[2]"/>
                  </xsl:call-template>
                </xsl:variable>
                <xsl:choose>
                  <xsl:when test="$i2=&quot;1&quot;">
                    <xsl:text>( </xsl:text>
                    <xsl:apply-templates select="*[2]/*[1]/*[2]/*[1]">
                      <xsl:with-param name="i" select="$i"/>
                      <xsl:with-param name="pr">
                        <xsl:text>1</xsl:text>
                      </xsl:with-param>
                    </xsl:apply-templates>
                    <xsl:text> iff </xsl:text>
                    <xsl:apply-templates select="*[2]/*[1]/*[1]">
                      <xsl:with-param name="i" select="$i"/>
                    </xsl:apply-templates>
                    <xsl:text> )</xsl:text>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:text>( </xsl:text>
                    <xsl:call-template name="ilist">
                      <xsl:with-param name="separ">
                        <xsl:text> &amp; </xsl:text>
                      </xsl:with-param>
                      <xsl:with-param name="elems" select="*"/>
                      <xsl:with-param name="i" select="$i"/>
                      <xsl:with-param name="pr">
                        <xsl:text>1</xsl:text>
                      </xsl:with-param>
                    </xsl:call-template>
                    <xsl:text> )</xsl:text>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text>( </xsl:text>
            <xsl:call-template name="ilist">
              <xsl:with-param name="separ">
                <xsl:text> &amp; </xsl:text>
              </xsl:with-param>
              <xsl:with-param name="elems" select="*"/>
              <xsl:with-param name="i" select="$i"/>
              <xsl:with-param name="pr">
                <xsl:text>1</xsl:text>
              </xsl:with-param>
            </xsl:call-template>
            <xsl:text> )</xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="Pred">
    <xsl:param name="i"/>
    <xsl:param name="not"/>
    <xsl:param name="pr"/>
    <xsl:choose>
      <xsl:when test="@kind=&apos;P&apos;">
        <xsl:call-template name="pschpvar">
          <xsl:with-param name="nr" select="@nr"/>
        </xsl:call-template>
        <xsl:text>[</xsl:text>
        <xsl:call-template name="list">
          <xsl:with-param name="separ">
            <xsl:text>,</xsl:text>
          </xsl:with-param>
          <xsl:with-param name="elems" select="*"/>
        </xsl:call-template>
        <xsl:text>]</xsl:text>
      </xsl:when>
      <xsl:when test="(@kind=&apos;V&apos;) or (@kind=&apos;R&apos;)">
        <xsl:variable name="pi">
          <xsl:call-template name="patt_info">
            <xsl:with-param name="k" select="@kind"/>
            <xsl:with-param name="nr" select="@nr"/>
            <xsl:with-param name="pid" select="@pid"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="fnr">
          <xsl:call-template name="car">
            <xsl:with-param name="l" select="$pi"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="antonym">
          <xsl:call-template name="cadr">
            <xsl:with-param name="l" select="$pi"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="plink">
          <xsl:call-template name="third">
            <xsl:with-param name="l" select="$pi"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="pid">
          <xsl:choose>
            <xsl:when test="$plink=&quot;1&quot;">
              <xsl:value-of select="@pid"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>0</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:variable name="predattr">
          <xsl:choose>
            <xsl:when test="$antonym&gt;1">
              <xsl:text>1</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>0</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:variable name="neg">
          <xsl:choose>
            <xsl:when test="$not=&quot;1&quot;">
              <xsl:value-of select="($antonym + $not) mod 2"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select="$antonym mod 2"/>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:if test="$neg=&quot;1&quot;">
          <xsl:text>not </xsl:text>
        </xsl:if>
        <xsl:choose>
          <xsl:when test="(@kind=&apos;V&apos;) and ($predattr=&quot;0&quot;)">
            <xsl:apply-templates select="*[position() = last()]"/>
            <xsl:text> is </xsl:text>
            <xsl:call-template name="abs">
              <xsl:with-param name="k" select="@kind"/>
              <xsl:with-param name="nr" select="@nr"/>
              <xsl:with-param name="sym">
                <xsl:call-template name="abs1">
                  <xsl:with-param name="k" select="@kind"/>
                  <xsl:with-param name="nr" select="@nr"/>
                  <xsl:with-param name="fnr" select="$fnr"/>
                  <xsl:with-param name="pid" select="$pid"/>
                </xsl:call-template>
              </xsl:with-param>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="pp">
              <xsl:with-param name="k" select="@kind"/>
              <xsl:with-param name="nr" select="@nr"/>
              <xsl:with-param name="args" select="*"/>
              <xsl:with-param name="pid" select="@pid"/>
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
    </xsl:choose>
  </xsl:template>

  <!-- ,#sym1=abs(#k=`@kind`, #nr=`@nr`, #sym=abs1(#k=`@kind`, #nr=`@nr`))); }} -->
  <!-- "[ "; list(#separ=",", #elems=`*`); "]"; } -->
  <xsl:template match="PrivPred">
    <xsl:param name="i"/>
    <xsl:param name="pr"/>
    <xsl:call-template name="pppred">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
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
    <xsl:param name="pr"/>
    <xsl:apply-templates select="*[1]"/>
    <xsl:text> is </xsl:text>
    <xsl:apply-templates select="*[2]"/>
  </xsl:template>

  <xsl:template match="Verum">
    <xsl:param name="i"/>
    <xsl:param name="pr"/>
    <xsl:text>verum</xsl:text>
  </xsl:template>

  <xsl:template match="ErrorFrm">
    <xsl:param name="i"/>
    <xsl:param name="pr"/>
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
        <xsl:call-template name="pschfvar">
          <xsl:with-param name="nr" select="@nr"/>
        </xsl:call-template>
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
          <xsl:with-param name="pid" select="@pid"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="PrivFunc">
    <xsl:param name="p"/>
    <xsl:call-template name="ppfunc">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
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
        <xsl:value-of select="concat(&quot;p&quot;,$paren_color)"/>
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
      <xsl:when test="(@kind=&quot;M&quot;) or (@kind=&quot;G&quot;)">
        <xsl:variable name="pi">
          <xsl:call-template name="patt_info">
            <xsl:with-param name="k" select="@kind"/>
            <xsl:with-param name="nr" select="@nr"/>
            <xsl:with-param name="pid" select="@pid"/>
          </xsl:call-template>
        </xsl:variable>
        <!-- DEBUG ":"; `@pid`; ":"; $pi; ":"; -->
        <xsl:variable name="fnr">
          <xsl:call-template name="car">
            <xsl:with-param name="l" select="$pi"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="expand">
          <xsl:call-template name="cadr">
            <xsl:with-param name="l" select="$pi"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="plink">
          <xsl:call-template name="third">
            <xsl:with-param name="l" select="$pi"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="k1">
          <xsl:choose>
            <xsl:when test="@kind=&quot;M&quot;">
              <xsl:text>M</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>L</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:choose>
          <xsl:when test="($expand=&quot;0&quot;) or not(@pid)">
            <xsl:call-template name="pp">
              <xsl:with-param name="k" select="$k1"/>
              <xsl:with-param name="nr" select="@nr"/>
              <xsl:with-param name="args" select="*[not(name()=&quot;Cluster&quot;)]"/>
              <xsl:with-param name="pid" select="@pid"/>
            </xsl:call-template>
          </xsl:when>
          <!-- abs(#k=$k1, #nr=`@nr`, #sym=abs1(#k=`@kind`, #nr=`@nr`, #fnr=$fnr)); -->
          <!-- if [count(*)>2] { " of "; list(#separ=",", -->
          <!-- #elems=`*[position()>$cluster_nr]`); } } -->
          <xsl:otherwise>
            <!-- abs(#k=$k1, #nr=`@nr`, #sym=abs1(#k=`@kind`, #nr=`@nr`, #fnr=$fnr)); -->
            <xsl:variable name="sym">
              <xsl:call-template name="abs1">
                <xsl:with-param name="k" select="@kind"/>
                <xsl:with-param name="nr" select="@nr"/>
                <xsl:with-param name="fnr" select="$fnr"/>
              </xsl:call-template>
            </xsl:variable>
            <xsl:variable name="vis">
              <xsl:call-template name="cdddr">
                <xsl:with-param name="l" select="$pi"/>
              </xsl:call-template>
            </xsl:variable>
            <xsl:variable name="el" select="."/>
            <!-- DEBUG ":"; `@pid`; ":"; $pi; ":"; -->
            <xsl:variable name="pid" select="@pid"/>
            <!-- apply[$el/*]; -->
            <!-- if [not(@pid)] -->
            <xsl:choose>
              <xsl:when test="key(&apos;EXP&apos;,$pid)">
                <xsl:for-each select="key(&apos;EXP&apos;,$pid)">
                  <xsl:variable name="alc">
                    <xsl:call-template name="lc">
                      <xsl:with-param name="s" select="@aid"/>
                    </xsl:call-template>
                  </xsl:variable>
                  <xsl:element name="a">
                    <xsl:attribute name="href">
                      <xsl:value-of select="concat($alc, &quot;.&quot;, $ext, &quot;#&quot;,&quot;NM&quot;,@nr)"/>
                    </xsl:attribute>
                    <xsl:if test="$titles=&quot;1&quot;">
                      <xsl:attribute name="title">
                        <xsl:value-of select="concat(@aid,&quot;:&quot;,&quot;NM&quot;,&quot;.&quot;,@nr)"/>
                      </xsl:attribute>
                    </xsl:if>
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
                  <xsl:if test="not($vis=&quot;&quot;)">
                    <xsl:text> of </xsl:text>
                    <xsl:call-template name="descent_many_vis">
                      <xsl:with-param name="patt" select="Expansion/Typ"/>
                      <xsl:with-param name="fix" select="$el"/>
                      <xsl:with-param name="vis" select="Visible/Int"/>
                    </xsl:call-template>
                  </xsl:if>
                </xsl:for-each>
              </xsl:when>
              <xsl:otherwise>
                <xsl:for-each select="document($patts,/)">
                  <xsl:if test="key(&apos;EXP&apos;,$pid)">
                    <xsl:for-each select="key(&apos;EXP&apos;,$pid)">
                      <xsl:variable name="alc">
                        <xsl:call-template name="lc">
                          <xsl:with-param name="s" select="@aid"/>
                        </xsl:call-template>
                      </xsl:variable>
                      <xsl:element name="a">
                        <xsl:attribute name="href">
                          <xsl:value-of select="concat($alc, &quot;.&quot;, $ext, &quot;#&quot;,&quot;NM&quot;,@nr)"/>
                        </xsl:attribute>
                        <xsl:if test="$titles=&quot;1&quot;">
                          <xsl:attribute name="title">
                            <xsl:value-of select="concat(@aid,&quot;:&quot;,&quot;NM&quot;,&quot;.&quot;,@nr)"/>
                          </xsl:attribute>
                        </xsl:if>
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
                      <xsl:if test="not($vis=&quot;&quot;)">
                        <xsl:text> of </xsl:text>
                        <xsl:call-template name="descent_many_vis">
                          <xsl:with-param name="patt" select="Expansion/Typ"/>
                          <xsl:with-param name="fix" select="$el"/>
                          <xsl:with-param name="vis" select="Visible/Int"/>
                        </xsl:call-template>
                      </xsl:if>
                    </xsl:for-each>
                  </xsl:if>
                </xsl:for-each>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <xsl:value-of select="@kind"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- gets two Typ, and list of Visible/Int; -->
  <!-- tries to find and print the terms in #fix corresponding -->
  <!-- to the visible loci; #patt is structurally similar to -->
  <!-- #fix, up to the loci -->
  <xsl:template name="descent_many_vis">
    <xsl:param name="patt"/>
    <xsl:param name="fix"/>
    <xsl:param name="vis"/>
    <xsl:if test="$vis">
      <xsl:variable name="v1" select="$vis[position()=1]/@x"/>
      <xsl:variable name="v2" select="$vis[position()&gt;1]"/>
      <!-- DEBUG    "descen:"; $v1; ":"; apply[$patt]; ":"; -->
      <xsl:call-template name="descent_many">
        <xsl:with-param name="patts" select="$patt/*[not(name()=&quot;Cluster&quot;)]"/>
        <xsl:with-param name="fixs" select="$fix/*[not(name()=&quot;Cluster&quot;)]"/>
        <xsl:with-param name="lnr" select="$v1"/>
        <xsl:with-param name="nr" select="count($patt/*[not(name()=&quot;Cluster&quot;)])"/>
      </xsl:call-template>
      <xsl:if test="$v2">
        <xsl:text>,</xsl:text>
        <xsl:call-template name="descent_many_vis">
          <xsl:with-param name="patt" select="$patt"/>
          <xsl:with-param name="fix" select="$fix"/>
          <xsl:with-param name="vis" select="$vis[position()&gt;1]"/>
        </xsl:call-template>
      </xsl:if>
    </xsl:if>
  </xsl:template>

  <xsl:template name="descent_many">
    <xsl:param name="patts"/>
    <xsl:param name="fixs"/>
    <xsl:param name="lnr"/>
    <xsl:param name="nr"/>
    <xsl:if test="$nr &gt; 0">
      <xsl:variable name="patt" select="$patts[position()=$nr]"/>
      <xsl:variable name="fix" select="$fixs[position()=$nr]"/>
      <!-- DEBUG "desone:"; $nr; ":"; `name($patt)`; ":"; `name($fix)`; ":"; -->
      <xsl:choose>
        <xsl:when test="(name($patt)=&quot;LocusVar&quot;) and ($patt/@nr=$lnr)">
          <!-- DEBUG    $lnr; ":"; `$patt/@nr`; ":";  "fff"; -->
          <xsl:for-each select="$top">
            <xsl:apply-templates select="$fix">
              <xsl:with-param name="p">
                <xsl:text>0</xsl:text>
              </xsl:with-param>
            </xsl:apply-templates>
          </xsl:for-each>
        </xsl:when>
        <!-- the duplication here is needed to generated the html properly; -->
        <!-- it does not cause any visible slowdown in practice -->
        <xsl:otherwise>
          <xsl:variable name="res">
            <xsl:choose>
              <xsl:when test="name($patt) = name($fix)">
                <xsl:call-template name="descent_many">
                  <xsl:with-param name="patts" select="$patt/*"/>
                  <xsl:with-param name="fixs" select="$fix/*"/>
                  <xsl:with-param name="lnr" select="$lnr"/>
                  <xsl:with-param name="nr" select="count($patt/*)"/>
                </xsl:call-template>
              </xsl:when>
              <xsl:otherwise>
                <xsl:text/>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:variable>
          <xsl:choose>
            <xsl:when test="$res and not($res=&quot;&quot;)">
              <!-- DEBUG [and contains($res,"fff")] -->
              <xsl:call-template name="descent_many">
                <xsl:with-param name="patts" select="$patt/*"/>
                <xsl:with-param name="fixs" select="$fix/*"/>
                <xsl:with-param name="lnr" select="$lnr"/>
                <xsl:with-param name="nr" select="count($patt/*)"/>
              </xsl:call-template>
            </xsl:when>
            <xsl:otherwise>
              <xsl:call-template name="descent_many">
                <xsl:with-param name="patts" select="$patts"/>
                <xsl:with-param name="fixs" select="$fixs"/>
                <xsl:with-param name="lnr" select="$lnr"/>
                <xsl:with-param name="nr" select="$nr - 1"/>
              </xsl:call-template>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:if>
  </xsl:template>

  <!-- Clusters -->
  <!-- only attributes with pid are now printed, others are results of -->
  <!-- cluster mechanisms -->
  <xsl:template match="Cluster">
    <xsl:call-template name="list">
      <xsl:with-param name="separ">
        <xsl:text> </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="*[@pid]"/>
    </xsl:call-template>
    <xsl:text> </xsl:text>
  </xsl:template>

  <!-- Adjective -->
  <xsl:template match="Adjective">
    <xsl:variable name="pi">
      <xsl:call-template name="patt_info">
        <xsl:with-param name="k">
          <xsl:text>V</xsl:text>
        </xsl:with-param>
        <xsl:with-param name="nr" select="@nr"/>
        <xsl:with-param name="pid" select="@pid"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="fnr">
      <xsl:call-template name="car">
        <xsl:with-param name="l" select="$pi"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="anto">
      <xsl:call-template name="cadr">
        <xsl:with-param name="l" select="$pi"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="plink">
      <xsl:call-template name="third">
        <xsl:with-param name="l" select="$pi"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="pid">
      <xsl:choose>
        <xsl:when test="$plink=&quot;1&quot;">
          <xsl:value-of select="@pid"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="neg">
      <xsl:choose>
        <xsl:when test="@value=&quot;false&quot;">
          <xsl:value-of select="($anto + 1) mod 2"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$anto mod 2"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:if test="$neg=&quot;1&quot;">
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
          <xsl:with-param name="fnr" select="$fnr"/>
          <xsl:with-param name="pid" select="$pid"/>
        </xsl:call-template>
      </xsl:with-param>
    </xsl:call-template>
  </xsl:template>

  <!-- if [count(*)>0] { "("; list(#separ=",", #elems=`*`); ")"; }} -->
  <xsl:template match="Proposition">
    <xsl:if test="following-sibling::*[1][(name()=&quot;By&quot;) and (@linked=&quot;true&quot;)]">
      <xsl:if test="not((name(..) = &quot;Consider&quot;) or (name(..) = &quot;Reconsider&quot;) 
              or (name(..) = &quot;Conclusion&quot;))">
        <xsl:element name="b">
          <xsl:text>then </xsl:text>
        </xsl:element>
      </xsl:if>
    </xsl:if>
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
    <xsl:param name="nbr"/>
    <xsl:if test="(count(*)&gt;0)">
      <xsl:element name="b">
        <xsl:text>by </xsl:text>
      </xsl:element>
      <xsl:element name="i">
        <xsl:call-template name="list">
          <xsl:with-param name="separ">
            <xsl:text>, </xsl:text>
          </xsl:with-param>
          <xsl:with-param name="elems" select="*"/>
        </xsl:call-template>
      </xsl:element>
    </xsl:if>
    <xsl:text>;</xsl:text>
    <xsl:if test="not($nbr=&quot;1&quot;)">
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="IterStep/By">
    <xsl:if test="(count(*)&gt;0)">
      <xsl:element name="b">
        <xsl:text>by </xsl:text>
      </xsl:element>
      <xsl:element name="i">
        <xsl:call-template name="list">
          <xsl:with-param name="separ">
            <xsl:text>, </xsl:text>
          </xsl:with-param>
          <xsl:with-param name="elems" select="*"/>
        </xsl:call-template>
      </xsl:element>
    </xsl:if>
  </xsl:template>

  <xsl:template match="From">
    <xsl:param name="nbr"/>
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
      <xsl:if test="not($nbr=&quot;1&quot;)">
        <xsl:element name="br"/>
      </xsl:if>
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
    <xsl:param name="nbr"/>
    <xsl:text>errorinference;</xsl:text>
    <xsl:if test="not($nbr=&quot;1&quot;)">
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="IterStep/ErrorInf">
    <xsl:text>errorinference</xsl:text>
  </xsl:template>

  <xsl:template match="SkippedProof">
    <xsl:param name="nbr"/>
    <xsl:element name="b">
      <xsl:text>@proof .. end;</xsl:text>
    </xsl:element>
    <xsl:if test="not($nbr=&quot;1&quot;)">
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="IterStep/SkippedProof">
    <xsl:element name="b">
      <xsl:text>@proof .. end;</xsl:text>
    </xsl:element>
  </xsl:template>

  <!-- Term, elIterStep+ -->
  <xsl:template match="IterEquality">
    <xsl:param name="nbr"/>
    <xsl:if test="IterStep[1]/By[@linked=&quot;true&quot;]">
      <xsl:if test="not(name(..)=&quot;Conclusion&quot;)">
        <xsl:element name="b">
          <xsl:text>then </xsl:text>
        </xsl:element>
      </xsl:if>
    </xsl:if>
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
    <xsl:if test="not($nbr=&quot;1&quot;)">
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="IterStep">
    <xsl:apply-templates/>
  </xsl:template>

  <!-- Skeleton steps -->
  <!-- tpl [Let] { $j=`@nr`; <b { "let "; } pconst(#nr=$j); -->
  <!-- " be "; -->
  <!-- jlist(#j=$j, #sep2=" be ", #elems=`*`); -->
  <!-- ";"; try_th_exps(#el=`.`); <br; } -->
  <!-- #fst tells to process in a sequence of Let's -->
  <!-- #beg is the beginning of const. sequence numbers -->
  <xsl:template match="Let">
    <xsl:param name="fst"/>
    <xsl:param name="beg"/>
    <xsl:variable name="has_thesis">
      <xsl:choose>
        <xsl:when test="following-sibling::*[1][name()=&quot;Thesis&quot;]">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="it_step">
      <xsl:choose>
        <xsl:when test="$has_thesis=&quot;1&quot;">
          <xsl:text>2</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>1</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:choose>
      <xsl:when test="not($fst=&quot;1&quot;) and (preceding-sibling::*[position()=$it_step][name()=&quot;Let&quot;])"/>
      <xsl:otherwise>
        <xsl:variable name="next">
          <xsl:choose>
            <xsl:when test="(count(Typ)=1) and 
     (following-sibling::*[position()=$it_step][name()=&quot;Let&quot;][count(Typ)=1]) and
     (($has_thesis=&quot;0&quot;) or 
     ((following-sibling::*[1][name()=&quot;Thesis&quot;][not(ThesisExpansions/Pair)]) 
     and
     (following-sibling::*[3][name()=&quot;Thesis&quot;][not(ThesisExpansions/Pair)])))">
              <xsl:call-template name="are_equal">
                <xsl:with-param name="el1" select="./Typ"/>
                <xsl:with-param name="el2" select="following-sibling::*[position()=$it_step]/Typ"/>
              </xsl:call-template>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>0</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:choose>
          <xsl:when test="$next=&quot;1&quot;">
            <xsl:variable name="beg1">
              <xsl:choose>
                <xsl:when test="$beg">
                  <xsl:value-of select="$beg"/>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:value-of select="@nr"/>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:variable>
            <xsl:apply-templates select="following-sibling::*[position()=$it_step]">
              <xsl:with-param name="fst">
                <xsl:text>1</xsl:text>
              </xsl:with-param>
              <xsl:with-param name="beg" select="$beg1"/>
            </xsl:apply-templates>
          </xsl:when>
          <xsl:otherwise>
            <xsl:choose>
              <xsl:when test="$beg">
                <xsl:element name="b">
                  <xsl:text>let </xsl:text>
                </xsl:element>
                <xsl:call-template name="ft_clist">
                  <xsl:with-param name="f" select="$beg"/>
                  <xsl:with-param name="t" select="@nr"/>
                  <xsl:with-param name="sep">
                    <xsl:text>, </xsl:text>
                  </xsl:with-param>
                </xsl:call-template>
                <xsl:text> be </xsl:text>
                <xsl:apply-templates select="Typ"/>
                <xsl:text>;</xsl:text>
                <xsl:element name="br"/>
                <xsl:apply-templates select="following-sibling::*[position()=$it_step][name()=&quot;Let&quot;]">
                  <xsl:with-param name="fst">
                    <xsl:text>1</xsl:text>
                  </xsl:with-param>
                </xsl:apply-templates>
              </xsl:when>
              <xsl:otherwise>
                <xsl:variable name="j" select="@nr - 1"/>
                <xsl:element name="b">
                  <xsl:text>let </xsl:text>
                </xsl:element>
                <xsl:call-template name="jtlist">
                  <xsl:with-param name="j" select="$j"/>
                  <xsl:with-param name="sep2">
                    <xsl:text> be </xsl:text>
                  </xsl:with-param>
                  <xsl:with-param name="elems" select="Typ"/>
                </xsl:call-template>
                <xsl:text>;</xsl:text>
                <xsl:call-template name="try_th_exps">
                  <xsl:with-param name="el" select="."/>
                </xsl:call-template>
                <xsl:element name="br"/>
                <xsl:if test="following-sibling::*[position()=$it_step][name()=&quot;Let&quot;]">
                  <xsl:apply-templates select="following-sibling::*[position()=$it_step]">
                    <xsl:with-param name="fst">
                      <xsl:text>1</xsl:text>
                    </xsl:with-param>
                  </xsl:apply-templates>
                </xsl:if>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="Assume">
    <xsl:element name="b">
      <xsl:text>assume </xsl:text>
    </xsl:element>
    <xsl:if test="count(*)&gt;1">
      <xsl:element name="b">
        <xsl:text>that </xsl:text>
      </xsl:element>
      <xsl:element name="br"/>
    </xsl:if>
    <xsl:call-template name="andlist">
      <xsl:with-param name="elems" select="*"/>
    </xsl:call-template>
    <xsl:text>;</xsl:text>
    <xsl:call-template name="try_th_exps">
      <xsl:with-param name="el" select="."/>
    </xsl:call-template>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="Given">
    <xsl:variable name="j" select="@nr - 1"/>
    <xsl:element name="b">
      <xsl:text>given </xsl:text>
    </xsl:element>
    <xsl:call-template name="jtlist">
      <xsl:with-param name="j" select="$j"/>
      <xsl:with-param name="sep2">
        <xsl:text> being </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="Typ"/>
    </xsl:call-template>
    <xsl:element name="b">
      <xsl:text> such that </xsl:text>
    </xsl:element>
    <xsl:call-template name="andlist">
      <xsl:with-param name="elems" select="Proposition"/>
    </xsl:call-template>
    <xsl:text>;</xsl:text>
    <xsl:call-template name="try_th_exps">
      <xsl:with-param name="el" select="."/>
    </xsl:call-template>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="Take">
    <xsl:element name="b">
      <xsl:text>take </xsl:text>
    </xsl:element>
    <xsl:apply-templates/>
    <xsl:text>;</xsl:text>
    <xsl:call-template name="try_th_exps">
      <xsl:with-param name="el" select="."/>
    </xsl:call-template>
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
    <xsl:call-template name="try_th_exps">
      <xsl:with-param name="el" select="."/>
    </xsl:call-template>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="Conclusion">
    <xsl:choose>
      <xsl:when test="(By[@linked=&quot;true&quot;]) or 
		   (IterEquality/IterStep[1]/By[@linked=&quot;true&quot;])">
        <xsl:element name="b">
          <xsl:text>hence </xsl:text>
        </xsl:element>
        <xsl:apply-templates select="*[not(name()=&quot;By&quot;)]"/>
        <xsl:apply-templates select="By">
          <xsl:with-param name="nbr">
            <xsl:text>1</xsl:text>
          </xsl:with-param>
        </xsl:apply-templates>
        <xsl:call-template name="try_th_exps">
          <xsl:with-param name="el" select="."/>
        </xsl:call-template>
        <xsl:element name="br"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="Now">
            <xsl:element name="div">
              <xsl:element name="b">
                <xsl:text>hereby </xsl:text>
              </xsl:element>
              <xsl:call-template name="try_th_exps">
                <xsl:with-param name="el" select="."/>
              </xsl:call-template>
              <xsl:apply-templates>
                <xsl:with-param name="nkw">
                  <xsl:text>1</xsl:text>
                </xsl:with-param>
              </xsl:apply-templates>
              <xsl:element name="b">
                <xsl:text>end;</xsl:text>
              </xsl:element>
            </xsl:element>
          </xsl:when>
          <xsl:otherwise>
            <xsl:element name="b">
              <xsl:text>thus </xsl:text>
            </xsl:element>
            <xsl:choose>
              <xsl:when test="Proof">
                <xsl:apply-templates select="Proposition"/>
                <xsl:call-template name="try_th_exps">
                  <xsl:with-param name="el" select="."/>
                </xsl:call-template>
                <xsl:apply-templates select="Proof"/>
              </xsl:when>
              <xsl:otherwise>
                <xsl:apply-templates select="Proposition"/>
                <xsl:apply-templates select=" IterEquality|By|From|ErrorInf
				   |SkippedProof">
                  <xsl:with-param name="nbr">
                    <xsl:text>1</xsl:text>
                  </xsl:with-param>
                </xsl:apply-templates>
                <xsl:call-template name="try_th_exps">
                  <xsl:with-param name="el" select="."/>
                </xsl:call-template>
                <xsl:element name="br"/>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="Case">
    <xsl:element name="b">
      <xsl:text>case </xsl:text>
    </xsl:element>
    <xsl:if test="count(*)&gt;1">
      <xsl:element name="b">
        <xsl:text>that </xsl:text>
      </xsl:element>
    </xsl:if>
    <xsl:call-template name="andlist">
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
      <xsl:element name="b">
        <xsl:text>that </xsl:text>
      </xsl:element>
    </xsl:if>
    <xsl:call-template name="andlist">
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
    <xsl:variable name="j" select="@nr - 1"/>
    <xsl:element name="b">
      <xsl:if test="By[@linked=&quot;true&quot;]">
        <xsl:text>then </xsl:text>
      </xsl:if>
      <xsl:text>consider </xsl:text>
    </xsl:element>
    <xsl:call-template name="jtlist">
      <xsl:with-param name="j" select="$j"/>
      <xsl:with-param name="sep2">
        <xsl:text> being </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="Typ"/>
    </xsl:call-template>
    <xsl:if test="count(Proposition) &gt; 1">
      <xsl:element name="b">
        <xsl:text> such that </xsl:text>
      </xsl:element>
      <xsl:element name="br"/>
      <xsl:call-template name="andlist">
        <xsl:with-param name="elems" select="Proposition[position() &gt; 1]"/>
      </xsl:call-template>
    </xsl:if>
    <xsl:apply-templates select="*[2]"/>
  </xsl:template>

  <xsl:template match="Reconsider">
    <xsl:variable name="j" select="@nr"/>
    <xsl:element name="b">
      <xsl:if test="By[@linked=&quot;true&quot;]">
        <xsl:text>then </xsl:text>
      </xsl:if>
      <xsl:text>reconsider </xsl:text>
    </xsl:element>
    <xsl:call-template name="pconst">
      <xsl:with-param name="nr" select="$j"/>
    </xsl:call-template>
    <xsl:text> = </xsl:text>
    <xsl:call-template name="jlist">
      <xsl:with-param name="j" select="$j"/>
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
      <xsl:text>deffunc </xsl:text>
    </xsl:element>
    <xsl:call-template name="ppfunc">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
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
    <xsl:apply-templates select="*[3]"/>
    <xsl:text> = </xsl:text>
    <xsl:apply-templates select="*[2]"/>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="DefPred">
    <xsl:element name="b">
      <xsl:text>defpred </xsl:text>
    </xsl:element>
    <xsl:call-template name="pppred">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
    <xsl:text>[</xsl:text>
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
  <!-- forbid as default -->
  <xsl:template match="Thesis"/>

  <xsl:template name="try_th_exps">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:apply-templates select="./following-sibling::*[1][name()=&quot;Thesis&quot;]/ThesisExpansions"/>
    </xsl:for-each>
  </xsl:template>

  <xsl:template match="ThesisExpansions">
    <xsl:if test="Pair">
      <xsl:text> </xsl:text>
      <xsl:call-template name="pcomment0">
        <xsl:with-param name="str">
          <xsl:text>according to </xsl:text>
        </xsl:with-param>
      </xsl:call-template>
      <xsl:call-template name="list">
        <xsl:with-param name="separ">
          <xsl:text>,</xsl:text>
        </xsl:with-param>
        <xsl:with-param name="elems" select="Pair[@x]"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>

  <xsl:template match="ThesisExpansions/Pair">
    <xsl:variable name="x" select="@x"/>
    <xsl:choose>
      <xsl:when test="key(&apos;DF&apos;,$x)">
        <xsl:for-each select="key(&apos;DF&apos;,$x)">
          <xsl:call-template name="mkref">
            <xsl:with-param name="aid" select="@aid"/>
            <xsl:with-param name="nr" select="@defnr"/>
            <xsl:with-param name="k">
              <xsl:text>D</xsl:text>
            </xsl:with-param>
            <xsl:with-param name="c">
              <xsl:text>1</xsl:text>
            </xsl:with-param>
          </xsl:call-template>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <xsl:for-each select="document($dfs,/)">
          <xsl:for-each select="key(&apos;DF&apos;,$x)">
            <xsl:call-template name="mkref">
              <xsl:with-param name="aid" select="@aid"/>
              <xsl:with-param name="nr" select="@defnr"/>
              <xsl:with-param name="k">
                <xsl:text>D</xsl:text>
              </xsl:with-param>
            </xsl:call-template>
          </xsl:for-each>
        </xsl:for-each>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- Registrations -->
  <xsl:template match="RCluster">
    <xsl:if test="$mml=&quot;1&quot;">
      <xsl:apply-templates select="ArgTypes"/>
    </xsl:if>
    <xsl:variable name="nr1" select="1 + count(preceding::RCluster)"/>
    <xsl:element name="a">
      <xsl:attribute name="NAME">
        <xsl:value-of select="concat(&quot;RC&quot;,$nr1)"/>
      </xsl:attribute>
      <xsl:element name="b">
        <xsl:text>cluster </xsl:text>
      </xsl:element>
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
    <xsl:if test="$mml=&quot;1&quot;">
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="CCluster">
    <xsl:if test="$mml=&quot;1&quot;">
      <xsl:apply-templates select="ArgTypes"/>
    </xsl:if>
    <xsl:variable name="nr1" select="1 + count(preceding::CCluster)"/>
    <xsl:element name="a">
      <xsl:attribute name="NAME">
        <xsl:value-of select="concat(&quot;CC&quot;,$nr1)"/>
      </xsl:attribute>
      <xsl:element name="b">
        <xsl:text>cluster </xsl:text>
      </xsl:element>
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
    <xsl:if test="$mml=&quot;1&quot;">
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="FCluster">
    <xsl:if test="$mml=&quot;1&quot;">
      <xsl:apply-templates select="ArgTypes"/>
    </xsl:if>
    <xsl:variable name="nr1" select="1 + count(preceding::FCluster)"/>
    <xsl:element name="a">
      <xsl:attribute name="NAME">
        <xsl:value-of select="concat(&quot;FC&quot;,$nr1)"/>
      </xsl:attribute>
      <xsl:element name="b">
        <xsl:text>cluster </xsl:text>
      </xsl:element>
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
    <xsl:if test="$mml=&quot;1&quot;">
      <xsl:element name="br"/>
    </xsl:if>
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
      <xsl:element name="a">
        <xsl:call-template name="add_hs2_attrs"/>
        <xsl:element name="b">
          <xsl:text>proof </xsl:text>
        </xsl:element>
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
  <!-- #nkw tells not to print the keword (used if hereby was printed above) -->
  <xsl:template match="Now">
    <xsl:param name="nkw"/>
    <xsl:choose>
      <xsl:when test="not($nkw=&quot;1&quot;)">
        <xsl:element name="div">
          <xsl:if test="@nr&gt;0">
            <xsl:call-template name="plab">
              <xsl:with-param name="nr" select="@nr"/>
            </xsl:call-template>
            <xsl:text>: </xsl:text>
          </xsl:if>
          <xsl:element name="a">
            <xsl:call-template name="add_hs2_attrs"/>
            <xsl:element name="b">
              <xsl:text>now </xsl:text>
            </xsl:element>
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
      </xsl:when>
      <xsl:otherwise>
        <xsl:element name="div">
          <xsl:attribute name="class">
            <xsl:text>add</xsl:text>
          </xsl:attribute>
          <xsl:apply-templates select="BlockThesis"/>
          <xsl:apply-templates select="*[not(name()=&apos;BlockThesis&apos;)]"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- tpl [Now](#nkw) { -->
  <!-- <div { <b { if [not($nkw="1")] { "now ";} } -->
  <!-- <div { @class="add"; apply[BlockThesis]; -->
  <!-- apply[*[not(name()='BlockThesis')]]; } -->
  <!-- <b { "end;"; } } } -->
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
    <xsl:variable name="nr1" select="1+count(preceding-sibling::JustifiedTheorem)"/>
    <xsl:element name="a">
      <xsl:attribute name="NAME">
        <xsl:value-of select="concat(&quot;T&quot;,$nr1)"/>
      </xsl:attribute>
      <xsl:call-template name="pcomment">
        <xsl:with-param name="str" select="concat($aname,&quot;:&quot;,$nr1)"/>
      </xsl:call-template>
    </xsl:element>
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
          <xsl:choose>
            <xsl:when test="Proposition/Verum">
              <xsl:element name="b">
                <xsl:text>canceled; </xsl:text>
              </xsl:element>
            </xsl:when>
            <xsl:otherwise>
              <xsl:apply-templates select="*[1]/*[1]"/>
              <xsl:text> </xsl:text>
              <xsl:apply-templates select="*[2]"/>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="DefTheorem">
    <xsl:variable name="nr1" select="1+count(preceding-sibling::DefTheorem)"/>
    <xsl:text>:: </xsl:text>
    <xsl:element name="b">
      <xsl:text>deftheorem </xsl:text>
    </xsl:element>
    <xsl:for-each select="Proposition[@nr &gt; 0]">
      <xsl:call-template name="plab">
        <xsl:with-param name="nr" select="@nr"/>
      </xsl:call-template>
    </xsl:for-each>
    <xsl:text> </xsl:text>
    <!-- <a { @NAME=`concat("D",$nr1)`; -->
    <xsl:if test="@constrkind">
      <xsl:text>  defines </xsl:text>
      <xsl:call-template name="abs">
        <xsl:with-param name="k" select="@constrkind"/>
        <xsl:with-param name="nr" select="@constrnr"/>
        <xsl:with-param name="sym">
          <xsl:call-template name="abs1">
            <xsl:with-param name="k" select="@constrkind"/>
            <xsl:with-param name="nr" select="@constrnr"/>
          </xsl:call-template>
        </xsl:with-param>
      </xsl:call-template>
    </xsl:if>
    <xsl:text> </xsl:text>
    <xsl:element name="a">
      <xsl:attribute name="onclick">
        <xsl:text>hs(this)</xsl:text>
      </xsl:attribute>
      <xsl:attribute name="href">
        <xsl:text>javascript:()</xsl:text>
      </xsl:attribute>
      <xsl:value-of select="concat($aname,&quot;:def &quot;,$nr1)"/>
      <xsl:text> : </xsl:text>
      <xsl:element name="br"/>
    </xsl:element>
    <xsl:element name="span">
      <xsl:attribute name="class">
        <xsl:text>hide</xsl:text>
      </xsl:attribute>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:choose>
          <xsl:when test="Proposition/Verum">
            <xsl:element name="b">
              <xsl:text>canceled; </xsl:text>
            </xsl:element>
          </xsl:when>
          <xsl:otherwise>
            <xsl:apply-templates select="*[1]/*[1]"/>
            <xsl:text>;</xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <xsl:template name="add_hs_attrs">
    <xsl:attribute name="class">
      <xsl:text>txt</xsl:text>
    </xsl:attribute>
    <xsl:attribute name="onclick">
      <xsl:text>hs(this)</xsl:text>
    </xsl:attribute>
    <xsl:attribute name="href">
      <xsl:text>javascript:()</xsl:text>
    </xsl:attribute>
  </xsl:template>

  <xsl:template name="add_hs2_attrs">
    <xsl:attribute name="class">
      <xsl:text>txt</xsl:text>
    </xsl:attribute>
    <xsl:attribute name="onclick">
      <xsl:text>hs2(this)</xsl:text>
    </xsl:attribute>
    <xsl:attribute name="href">
      <xsl:text>javascript:()</xsl:text>
    </xsl:attribute>
  </xsl:template>

  <!-- Property, elProposition, Justification -->
  <xsl:template match="JustifiedProperty">
    <xsl:element name="a">
      <xsl:call-template name="add_hs_attrs"/>
      <xsl:element name="b">
        <xsl:value-of select="translate(name(*[1]), $ucletters, $lcletters)"/>
        <xsl:text> </xsl:text>
      </xsl:element>
    </xsl:element>
    <xsl:element name="span">
      <xsl:attribute name="class">
        <xsl:text>hide</xsl:text>
      </xsl:attribute>
      <xsl:element name="br"/>
      <xsl:apply-templates select="*[2]"/>
    </xsl:element>
    <xsl:apply-templates select="*[position()&gt;2]"/>
  </xsl:template>

  <!-- Formula | ( elProposition, Justification ) -->
  <xsl:template match="UnknownCorrCond|Coherence|Compatibility|Consistency|Existence|Uniqueness">
    <xsl:element name="a">
      <xsl:call-template name="add_hs_attrs"/>
      <xsl:element name="b">
        <xsl:value-of select="translate(name(), $ucletters, $lcletters)"/>
        <xsl:text> </xsl:text>
      </xsl:element>
    </xsl:element>
    <!-- <br; -->
    <xsl:element name="span">
      <xsl:attribute name="class">
        <xsl:text>hide</xsl:text>
      </xsl:attribute>
      <xsl:element name="br"/>
      <xsl:apply-templates select="*[1]"/>
    </xsl:element>
    <xsl:choose>
      <xsl:when test="count(*)&gt;1">
        <xsl:apply-templates select="*[position()&gt;1]"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>;</xsl:text>
        <xsl:element name="br"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- CorrectnessCondition*, elProposition, Justification -->
  <xsl:template match="Correctness">
    <xsl:element name="a">
      <xsl:call-template name="add_hs_attrs"/>
      <xsl:element name="b">
        <xsl:text>correctness </xsl:text>
      </xsl:element>
    </xsl:element>
    <!-- apply to subconditions , skip their conjunction -->
    <xsl:element name="span">
      <xsl:attribute name="class">
        <xsl:text>hide</xsl:text>
      </xsl:attribute>
      <xsl:element name="br"/>
      <xsl:apply-templates select="*[position()&lt;(last()-1)]"/>
    </xsl:element>
    <xsl:apply-templates select="*[position()=last()]"/>
  </xsl:template>

  <xsl:template match="Canceled">
    <xsl:element name="b">
      <xsl:text>canceled;</xsl:text>
    </xsl:element>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="SchemeFuncDecl">
    <xsl:call-template name="pschfvar">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
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
    <xsl:call-template name="pschpvar">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
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
      <xsl:element name="a">
        <xsl:attribute name="NAME">
          <xsl:value-of select="concat(&quot;S&quot;,@schemenr)"/>
        </xsl:attribute>
        <xsl:element name="b">
          <xsl:text>scheme  </xsl:text>
        </xsl:element>
        <xsl:call-template name="pcomment">
          <xsl:with-param name="str" select="concat($aname,&quot;:sch &quot;,@schemenr)"/>
        </xsl:call-template>
      </xsl:element>
      <xsl:text>s</xsl:text>
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
  <!-- elJustifiedProperty*, elConstructor?, elPattern? ) -->
  <!-- | ( elConstructor, elConstructor, elConstructor+, -->
  <!-- elRegistration, CorrectnessCondition*, -->
  <!-- elCorrectness?, elPattern+ )) -->
  <!-- ##TODO: commented registartion and strict attr for defstruct -->
  <xsl:template match="Definition">
    <xsl:choose>
      <xsl:when test="@expandable=&quot;true&quot;">
        <xsl:for-each select="Pattern">
          <xsl:element name="a">
            <xsl:attribute name="NAME">
              <xsl:value-of select="concat(&quot;NM&quot;,@nr)"/>
            </xsl:attribute>
            <xsl:element name="b">
              <xsl:text>mode </xsl:text>
            </xsl:element>
            <xsl:call-template name="abs1">
              <xsl:with-param name="k">
                <xsl:text>M</xsl:text>
              </xsl:with-param>
              <xsl:with-param name="fnr" select="@formatnr"/>
            </xsl:call-template>
            <xsl:element name="b">
              <xsl:text> is </xsl:text>
            </xsl:element>
          </xsl:element>
          <xsl:apply-templates select="Expansion/Typ"/>
          <xsl:text>;</xsl:text>
          <xsl:element name="br"/>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <xsl:variable name="nl">
          <xsl:choose>
            <xsl:when test="@nr">
              <xsl:text>0</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>1</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <!-- Constructor may be missing, if this is a redefinition -->
        <!-- that does not change its types. In that case, the Constructor needs -->
        <!-- to be retrieved from the Definiens - see below. -->
        <xsl:apply-templates select="Constructor">
          <xsl:with-param name="indef">
            <xsl:text>1</xsl:text>
          </xsl:with-param>
          <xsl:with-param name="nl" select="$nl"/>
        </xsl:apply-templates>
        <!-- @nr is present iff Definiens is present; it can be 0 if -->
        <!-- the deiniens is not labeled, otherwise it is the proposition number -->
        <!-- of its deftheorem -->
        <xsl:if test="@nr">
          <xsl:variable name="nr1" select="@nr"/>
          <xsl:variable name="cnt1" select="1 + count(preceding-sibling::Definition[@nr])"/>
          <xsl:variable name="cnstr" select="count(Constructor)"/>
          <xsl:for-each select="../following-sibling::Definiens[position()=$cnt1]">
            <xsl:variable name="ckind" select="@constrkind"/>
            <xsl:variable name="cnr" select="@constrnr"/>
            <xsl:if test="$cnstr=0">
              <!-- here the redefined constructor is retrieved from definiens -->
              <xsl:element name="b">
                <xsl:text>redefine </xsl:text>
              </xsl:element>
              <xsl:choose>
                <xsl:when test="key($ckind,$cnr)">
                  <xsl:apply-templates select="key($ckind,$cnr)">
                    <xsl:with-param name="indef">
                      <xsl:text>1</xsl:text>
                    </xsl:with-param>
                    <xsl:with-param name="nl" select="$nl"/>
                  </xsl:apply-templates>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:for-each select="document($constrs,/)">
                    <xsl:apply-templates select="key($ckind,$cnr)">
                      <xsl:with-param name="indef">
                        <xsl:text>1</xsl:text>
                      </xsl:with-param>
                      <xsl:with-param name="nl" select="$nl"/>
                    </xsl:apply-templates>
                  </xsl:for-each>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:if>
            <xsl:element name="b">
              <xsl:choose>
                <xsl:when test="DefMeaning/@kind=&apos;e&apos;">
                  <xsl:text> equals </xsl:text>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:text> means </xsl:text>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:element>
            <xsl:if test="$nr1&gt;0">
              <xsl:text>:</xsl:text>
              <xsl:call-template name="plab">
                <xsl:with-param name="nr" select="$nr1"/>
              </xsl:call-template>
              <xsl:text>: </xsl:text>
            </xsl:if>
            <xsl:element name="a">
              <xsl:attribute name="NAME">
                <xsl:value-of select="concat(&quot;D&quot;,@defnr)"/>
              </xsl:attribute>
              <xsl:call-template name="pcomment">
                <xsl:with-param name="str" select="concat($aname,&quot;:def &quot;,@defnr)"/>
              </xsl:call-template>
            </xsl:element>
            <!-- ":: "; `@aid`; ":def "; `@defnr`; <br; "  "; -->
            <xsl:for-each select="DefMeaning/PartialDef">
              <xsl:apply-templates select="*[1]"/>
              <xsl:element name="b">
                <xsl:text> if </xsl:text>
              </xsl:element>
              <xsl:apply-templates select="*[2]"/>
              <xsl:element name="br"/>
            </xsl:for-each>
            <xsl:if test="(DefMeaning/PartialDef) 
	    and (DefMeaning/*[(position() = last()) 
		and not(name()=&quot;PartialDef&quot;)])">
              <xsl:element name="b">
                <xsl:text> otherwise </xsl:text>
              </xsl:element>
            </xsl:if>
            <xsl:apply-templates select="DefMeaning/*[(position() = last()) 
	                     and not(name()=&quot;PartialDef&quot;)]"/>
            <xsl:text>;</xsl:text>
            <xsl:element name="br"/>
          </xsl:for-each>
        </xsl:if>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:apply-templates select="*[not((name()=&apos;Constructor&apos;) or (name()=&apos;Pattern&apos;) 
                or (name()=&apos;Registration&apos;))]"/>
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

  <xsl:template name="lc">
    <xsl:param name="s"/>
    <xsl:value-of select="translate($s, $ucletters, $lcletters)"/>
  </xsl:template>

  <xsl:template name="uc">
    <xsl:param name="s"/>
    <xsl:value-of select="translate($s, $lcletters, $ucletters)"/>
  </xsl:template>
  <!-- poor man's data structure, aka "colon-list" -->
  <xsl:param name="nil">
    <xsl:text/>
  </xsl:param>

  <xsl:template name="cons">
    <xsl:param name="h"/>
    <xsl:param name="t"/>
    <xsl:value-of select="concat($h,&quot;:&quot;,$t)"/>
  </xsl:template>

  <xsl:template name="car">
    <xsl:param name="l"/>
    <xsl:value-of select="substring-before($l,&quot;:&quot;)"/>
  </xsl:template>

  <xsl:template name="cdr">
    <xsl:param name="l"/>
    <xsl:value-of select="substring-after($l,&quot;:&quot;)"/>
  </xsl:template>

  <xsl:template name="cadr">
    <xsl:param name="l"/>
    <xsl:call-template name="car">
      <xsl:with-param name="l">
        <xsl:call-template name="cdr">
          <xsl:with-param name="l" select="$l"/>
        </xsl:call-template>
      </xsl:with-param>
    </xsl:call-template>
  </xsl:template>

  <xsl:template name="cddr">
    <xsl:param name="l"/>
    <xsl:call-template name="cdr">
      <xsl:with-param name="l">
        <xsl:call-template name="cdr">
          <xsl:with-param name="l" select="$l"/>
        </xsl:call-template>
      </xsl:with-param>
    </xsl:call-template>
  </xsl:template>

  <xsl:template name="third">
    <xsl:param name="l"/>
    <xsl:call-template name="car">
      <xsl:with-param name="l">
        <xsl:call-template name="cddr">
          <xsl:with-param name="l" select="$l"/>
        </xsl:call-template>
      </xsl:with-param>
    </xsl:call-template>
  </xsl:template>

  <xsl:template name="cdddr">
    <xsl:param name="l"/>
    <xsl:call-template name="cdr">
      <xsl:with-param name="l">
        <xsl:call-template name="cddr">
          <xsl:with-param name="l" select="$l"/>
        </xsl:call-template>
      </xsl:with-param>
    </xsl:call-template>
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

  <!-- List utility with additional arg - now only used for formula lists -->
  <xsl:template name="ilist">
    <xsl:param name="separ"/>
    <xsl:param name="elems"/>
    <xsl:param name="i"/>
    <xsl:param name="pr"/>
    <xsl:for-each select="$elems">
      <xsl:apply-templates select=".">
        <xsl:with-param name="i" select="$i"/>
        <xsl:with-param name="pr" select="$pr"/>
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

  <!-- newlined andlist -->
  <xsl:template name="andlist">
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:apply-templates select="."/>
      <xsl:if test="not(position()=last())">
        <xsl:element name="b">
          <xsl:text>and </xsl:text>
        </xsl:element>
        <xsl:element name="br"/>
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

  <xsl:template name="jtlist">
    <xsl:param name="j"/>
    <xsl:param name="sep2"/>
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:call-template name="pconst">
        <xsl:with-param name="nr" select="$j+position()"/>
      </xsl:call-template>
      <xsl:choose>
        <xsl:when test="position()=last()">
          <xsl:value-of select="$sep2"/>
          <xsl:apply-templates select="."/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:variable name="eq1">
            <xsl:call-template name="are_equal">
              <xsl:with-param name="el1" select="."/>
              <xsl:with-param name="el2" select="following-sibling::*[1]"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:if test="$eq1=&quot;0&quot;">
            <xsl:value-of select="$sep2"/>
            <xsl:apply-templates select="."/>
          </xsl:if>
          <xsl:text>, </xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <!-- if [not(string() = string(following-sibling::*[1]))] -->
  <!-- add numbers starting at #j+1 between #sep1 and #sep2 - now with constants -->
  <xsl:template name="jlist">
    <xsl:param name="j"/>
    <xsl:param name="sep2"/>
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:apply-templates select="."/>
      <xsl:if test="not(position()=last())">
        <xsl:text>, </xsl:text>
        <xsl:call-template name="pconst">
          <xsl:with-param name="nr" select="$j+position()"/>
        </xsl:call-template>
        <xsl:value-of select="$sep2"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <!-- like jlist, but with loci -->
  <xsl:template name="alist">
    <xsl:param name="j"/>
    <xsl:param name="sep1"/>
    <xsl:param name="sep2"/>
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:apply-templates select="."/>
      <xsl:if test="not(position()=last())">
        <xsl:value-of select="$sep1"/>
        <xsl:call-template name="ploci">
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

  <!-- from-to list of consts starting numbering at $f ending at $t -->
  <xsl:template name="ft_clist">
    <xsl:param name="f"/>
    <xsl:param name="t"/>
    <xsl:param name="sep"/>
    <xsl:choose>
      <xsl:when test="$f = $t">
        <xsl:call-template name="pconst">
          <xsl:with-param name="nr" select="$f"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:if test="$f &lt; $t">
          <xsl:call-template name="pconst">
            <xsl:with-param name="nr" select="$f"/>
          </xsl:call-template>
          <xsl:value-of select="$sep"/>
          <xsl:call-template name="ft_clist">
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
  <!-- #pid links to  patterns instead of constructors -->
  <xsl:template name="absref">
    <xsl:param name="elems"/>
    <xsl:param name="c"/>
    <xsl:param name="sym"/>
    <xsl:param name="pid"/>
    <xsl:variable name="n">
      <xsl:choose>
        <xsl:when test="$pid&gt;0">
          <xsl:text>N</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:for-each select="$elems">
      <xsl:variable name="mk">
        <xsl:call-template name="mkind">
          <xsl:with-param name="kind" select="@kind"/>
          <xsl:with-param name="notat" select="$pid"/>
        </xsl:call-template>
      </xsl:variable>
      <xsl:variable name="alc">
        <xsl:call-template name="lc">
          <xsl:with-param name="s" select="@aid"/>
        </xsl:call-template>
      </xsl:variable>
      <xsl:element name="a">
        <xsl:choose>
          <xsl:when test="($linking = &apos;q&apos;) or (($linking = &apos;m&apos;) and not($c = &quot;1&quot;))">
            <!-- @onClick="l1(this.getAttribute('lu'))"; -->
            <!-- @lu = `concat(@aid,":",$mk,".",@nr)`; -->
            <!-- @href=`concat($alc, ".html#",@kind,@nr)`; -->
            <xsl:attribute name="href">
              <xsl:value-of select="concat($mmlq,@aid,&quot;:&quot;,$mk,&quot;.&quot;,@nr)"/>
            </xsl:attribute>
          </xsl:when>
          <xsl:otherwise>
            <xsl:attribute name="href">
              <xsl:value-of select="concat($alc, &quot;.&quot;, $ext, &quot;#&quot;,$n,@kind,@nr)"/>
            </xsl:attribute>
            <xsl:if test="$c">
              <xsl:attribute name="target">
                <xsl:text>_self</xsl:text>
              </xsl:attribute>
            </xsl:if>
          </xsl:otherwise>
        </xsl:choose>
        <xsl:if test="$titles=&quot;1&quot;">
          <xsl:attribute name="title">
            <xsl:value-of select="concat(@aid,&quot;:&quot;,$mk,&quot;.&quot;,@nr)"/>
          </xsl:attribute>
        </xsl:if>
        <xsl:choose>
          <xsl:when test="$sym">
            <xsl:value-of select="$sym"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:choose>
              <xsl:when test="$relnames&gt;0">
                <xsl:value-of select="$n"/>
                <xsl:value-of select="@kind"/>
                <xsl:value-of select="@relnr"/>
              </xsl:when>
              <xsl:otherwise>
                <xsl:value-of select="$n"/>
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
    <xsl:param name="pid"/>
    <xsl:param name="c1">
      <xsl:choose>
        <xsl:when test="$mml = &quot;1&quot;">
          <xsl:text>0</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>1</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:param>
    <xsl:choose>
      <xsl:when test="$pid&gt;0">
        <xsl:variable name="k1" select="concat(&apos;P_&apos;,$k)"/>
        <xsl:choose>
          <xsl:when test="key($k1,$nr)[$pid=@relnr]">
            <xsl:call-template name="absref">
              <xsl:with-param name="elems" select="key($k1,$nr)[$pid=@relnr]"/>
              <xsl:with-param name="c" select="$c1"/>
              <xsl:with-param name="sym" select="$sym"/>
              <xsl:with-param name="pid" select="$pid"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:for-each select="document($patts,/)">
              <xsl:call-template name="absref">
                <xsl:with-param name="elems" select="key($k1,$nr)[$pid=@relnr]"/>
                <xsl:with-param name="sym" select="$sym"/>
                <xsl:with-param name="pid" select="$pid"/>
              </xsl:call-template>
            </xsl:for-each>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="key($k,$nr)">
            <xsl:call-template name="absref">
              <xsl:with-param name="elems" select="key($k,$nr)"/>
              <xsl:with-param name="c" select="$c1"/>
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
    <xsl:param name="fnr"/>
    <xsl:param name="pid"/>
    <!-- DEBUG    "abs1:"; $k; ":"; $fnr; ":"; -->
    <xsl:variable name="fnr1">
      <xsl:choose>
        <xsl:when test="$fnr">
          <xsl:value-of select="$fnr"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:call-template name="formt_nr">
            <xsl:with-param name="k" select="$k"/>
            <xsl:with-param name="nr" select="$nr"/>
            <xsl:with-param name="pid" select="$pid"/>
          </xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:for-each select="document($formats,/)">
      <xsl:choose>
        <xsl:when test="not(key(&apos;F&apos;,$fnr1))">
          <xsl:value-of select="concat($k,$nr)"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:for-each select="key(&apos;F&apos;,$fnr1)">
            <xsl:variable name="snr" select="@symbolnr"/>
            <xsl:variable name="sk1" select="@kind"/>
            <xsl:variable name="sk">
              <xsl:choose>
                <xsl:when test="$sk1=&quot;L&quot;">
                  <xsl:text>G</xsl:text>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:value-of select="$sk1"/>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:variable>
            <xsl:variable name="dkey" select="concat(&apos;D_&apos;,$sk)"/>
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
    <xsl:param name="pid"/>
    <xsl:variable name="j">
      <xsl:call-template name="patt_info">
        <xsl:with-param name="k" select="$k"/>
        <xsl:with-param name="nr" select="$nr"/>
        <xsl:with-param name="pid" select="$pid"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:call-template name="car">
      <xsl:with-param name="l" select="$j"/>
    </xsl:call-template>
  </xsl:template>

  <xsl:template name="mk_vis_list">
    <xsl:param name="els"/>
    <!-- $t = mk_vis_list(#els=`$els[position()>1]`); -->
    <xsl:for-each select="$els">
      <xsl:value-of select="@x"/>
      <xsl:text>:</xsl:text>
    </xsl:for-each>
  </xsl:template>

  <!-- returns 2 * formatnr + 1 if antonymic or expandable; -->
  <!-- this is a small hack to minimize chasing patterns -->
  <xsl:template name="patt_info">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:param name="pid"/>
    <xsl:variable name="k1">
      <xsl:choose>
        <xsl:when test="$k=&quot;L&quot;">
          <xsl:text>G</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$k"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="md" select="($k1 = &quot;G&quot;) or ($k1=&quot;M&quot;)"/>
    <xsl:variable name="pkey" select="concat(&apos;P_&apos;,$k1)"/>
    <xsl:choose>
      <xsl:when test="$pid&gt;0">
        <xsl:choose>
          <xsl:when test="$md and key(&apos;EXP&apos;,$pid)">
            <xsl:for-each select="key(&apos;EXP&apos;,$pid)">
              <xsl:variable name="vis">
                <xsl:call-template name="mk_vis_list">
                  <xsl:with-param name="els" select="Visible/Int"/>
                </xsl:call-template>
              </xsl:variable>
              <xsl:call-template name="cons">
                <xsl:with-param name="h" select="@formatnr"/>
                <xsl:with-param name="t">
                  <xsl:call-template name="cons">
                    <xsl:with-param name="h">
                      <xsl:text>1</xsl:text>
                    </xsl:with-param>
                    <xsl:with-param name="t">
                      <xsl:call-template name="cons">
                        <xsl:with-param name="h">
                          <xsl:text>0</xsl:text>
                        </xsl:with-param>
                        <xsl:with-param name="t" select="$vis"/>
                      </xsl:call-template>
                    </xsl:with-param>
                  </xsl:call-template>
                </xsl:with-param>
              </xsl:call-template>
            </xsl:for-each>
          </xsl:when>
          <xsl:otherwise>
            <xsl:choose>
              <xsl:when test="key($pkey,$nr)[$pid=@relnr]">
                <xsl:for-each select="key($pkey,$nr)[$pid=@relnr]">
                  <xsl:variable name="shift0">
                    <xsl:choose>
                      <xsl:when test="@antonymic">
                        <xsl:text>1</xsl:text>
                      </xsl:when>
                      <xsl:otherwise>
                        <xsl:text>0</xsl:text>
                      </xsl:otherwise>
                    </xsl:choose>
                  </xsl:variable>
                  <xsl:variable name="shift">
                    <xsl:choose>
                      <xsl:when test="($k=&quot;V&quot;) and (@kind=&quot;R&quot;)">
                        <xsl:value-of select="2 + $shift0"/>
                      </xsl:when>
                      <xsl:otherwise>
                        <xsl:value-of select="$shift0"/>
                      </xsl:otherwise>
                    </xsl:choose>
                  </xsl:variable>
                  <xsl:variable name="plink">
                    <xsl:choose>
                      <xsl:when test="@redefnr&gt;0">
                        <xsl:text>1</xsl:text>
                      </xsl:when>
                      <xsl:otherwise>
                        <xsl:text>0</xsl:text>
                      </xsl:otherwise>
                    </xsl:choose>
                  </xsl:variable>
                  <xsl:variable name="vis">
                    <xsl:call-template name="mk_vis_list">
                      <xsl:with-param name="els" select="Visible/Int"/>
                    </xsl:call-template>
                  </xsl:variable>
                  <xsl:call-template name="cons">
                    <xsl:with-param name="h" select="@formatnr"/>
                    <xsl:with-param name="t">
                      <xsl:call-template name="cons">
                        <xsl:with-param name="h" select="$shift"/>
                        <xsl:with-param name="t">
                          <xsl:call-template name="cons">
                            <xsl:with-param name="h" select="$plink"/>
                            <xsl:with-param name="t" select="$vis"/>
                          </xsl:call-template>
                        </xsl:with-param>
                      </xsl:call-template>
                    </xsl:with-param>
                  </xsl:call-template>
                </xsl:for-each>
              </xsl:when>
              <xsl:otherwise>
                <xsl:for-each select="document($patts,/)">
                  <xsl:choose>
                    <xsl:when test="$md and key(&apos;EXP&apos;,$pid)">
                      <xsl:for-each select="key(&apos;EXP&apos;,$pid)">
                        <xsl:variable name="vis">
                          <xsl:call-template name="mk_vis_list">
                            <xsl:with-param name="els" select="Visible/Int"/>
                          </xsl:call-template>
                        </xsl:variable>
                        <xsl:call-template name="cons">
                          <xsl:with-param name="h" select="@formatnr"/>
                          <xsl:with-param name="t">
                            <xsl:call-template name="cons">
                              <xsl:with-param name="h">
                                <xsl:text>1</xsl:text>
                              </xsl:with-param>
                              <xsl:with-param name="t">
                                <xsl:call-template name="cons">
                                  <xsl:with-param name="h">
                                    <xsl:text>0</xsl:text>
                                  </xsl:with-param>
                                  <xsl:with-param name="t" select="$vis"/>
                                </xsl:call-template>
                              </xsl:with-param>
                            </xsl:call-template>
                          </xsl:with-param>
                        </xsl:call-template>
                      </xsl:for-each>
                    </xsl:when>
                    <xsl:otherwise>
                      <xsl:choose>
                        <xsl:when test="key($pkey,$nr)[$pid=@relnr]">
                          <xsl:for-each select="key($pkey,$nr)[$pid=@relnr]">
                            <xsl:variable name="shift0">
                              <xsl:choose>
                                <xsl:when test="@antonymic">
                                  <xsl:text>1</xsl:text>
                                </xsl:when>
                                <xsl:otherwise>
                                  <xsl:text>0</xsl:text>
                                </xsl:otherwise>
                              </xsl:choose>
                            </xsl:variable>
                            <xsl:variable name="shift">
                              <xsl:choose>
                                <xsl:when test="($k=&quot;V&quot;) and (@kind=&quot;R&quot;)">
                                  <xsl:value-of select="2 + $shift0"/>
                                </xsl:when>
                                <xsl:otherwise>
                                  <xsl:value-of select="$shift0"/>
                                </xsl:otherwise>
                              </xsl:choose>
                            </xsl:variable>
                            <xsl:variable name="plink">
                              <xsl:choose>
                                <xsl:when test="@redefnr&gt;0">
                                  <xsl:text>1</xsl:text>
                                </xsl:when>
                                <xsl:otherwise>
                                  <xsl:text>0</xsl:text>
                                </xsl:otherwise>
                              </xsl:choose>
                            </xsl:variable>
                            <xsl:variable name="vis">
                              <xsl:call-template name="mk_vis_list">
                                <xsl:with-param name="els" select="Visible/Int"/>
                              </xsl:call-template>
                            </xsl:variable>
                            <xsl:call-template name="cons">
                              <xsl:with-param name="h" select="@formatnr"/>
                              <xsl:with-param name="t">
                                <xsl:call-template name="cons">
                                  <xsl:with-param name="h" select="$shift"/>
                                  <xsl:with-param name="t">
                                    <xsl:call-template name="cons">
                                      <xsl:with-param name="h" select="$plink"/>
                                      <xsl:with-param name="t" select="$vis"/>
                                    </xsl:call-template>
                                  </xsl:with-param>
                                </xsl:call-template>
                              </xsl:with-param>
                            </xsl:call-template>
                          </xsl:for-each>
                        </xsl:when>
                        <xsl:otherwise>
                          <xsl:text>failedpid:</xsl:text>
                          <xsl:value-of select="$k1"/>
                          <xsl:text>:</xsl:text>
                          <xsl:value-of select="$nr"/>
                          <xsl:text>:</xsl:text>
                          <xsl:value-of select="$pid"/>
                          <xsl:text>:</xsl:text>
                        </xsl:otherwise>
                      </xsl:choose>
                    </xsl:otherwise>
                  </xsl:choose>
                </xsl:for-each>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="key($pkey,$nr)">
            <xsl:for-each select="key($pkey,$nr)[position()=1]">
              <xsl:variable name="shift0">
                <xsl:choose>
                  <xsl:when test="Expansion or @antonymic">
                    <xsl:text>1</xsl:text>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:text>0</xsl:text>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:variable>
              <xsl:variable name="shift">
                <xsl:choose>
                  <xsl:when test="($k=&quot;V&quot;) and (@kind=&quot;R&quot;)">
                    <xsl:value-of select="2 + $shift0"/>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:value-of select="$shift0"/>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:variable>
              <xsl:variable name="plink">
                <xsl:choose>
                  <xsl:when test="@redefnr&gt;0">
                    <xsl:text>1</xsl:text>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:text>0</xsl:text>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:variable>
              <xsl:variable name="vis">
                <xsl:call-template name="mk_vis_list">
                  <xsl:with-param name="els" select="Visible/Int"/>
                </xsl:call-template>
              </xsl:variable>
              <xsl:call-template name="cons">
                <xsl:with-param name="h" select="@formatnr"/>
                <xsl:with-param name="t">
                  <xsl:call-template name="cons">
                    <xsl:with-param name="h" select="$shift"/>
                    <xsl:with-param name="t">
                      <xsl:call-template name="cons">
                        <xsl:with-param name="h" select="$plink"/>
                        <xsl:with-param name="t" select="$vis"/>
                      </xsl:call-template>
                    </xsl:with-param>
                  </xsl:call-template>
                </xsl:with-param>
              </xsl:call-template>
            </xsl:for-each>
          </xsl:when>
          <xsl:otherwise>
            <xsl:for-each select="document($patts,/)">
              <xsl:for-each select="key($pkey,$nr)[position()=1]">
                <xsl:variable name="shift0">
                  <xsl:choose>
                    <xsl:when test="Expansion or @antonymic">
                      <xsl:text>1</xsl:text>
                    </xsl:when>
                    <xsl:otherwise>
                      <xsl:text>0</xsl:text>
                    </xsl:otherwise>
                  </xsl:choose>
                </xsl:variable>
                <xsl:variable name="shift">
                  <xsl:choose>
                    <xsl:when test="($k=&quot;V&quot;) and (@kind=&quot;R&quot;)">
                      <xsl:value-of select="2 + $shift0"/>
                    </xsl:when>
                    <xsl:otherwise>
                      <xsl:value-of select="$shift0"/>
                    </xsl:otherwise>
                  </xsl:choose>
                </xsl:variable>
                <xsl:variable name="plink">
                  <xsl:choose>
                    <xsl:when test="@redefnr&gt;0">
                      <xsl:text>1</xsl:text>
                    </xsl:when>
                    <xsl:otherwise>
                      <xsl:text>0</xsl:text>
                    </xsl:otherwise>
                  </xsl:choose>
                </xsl:variable>
                <xsl:variable name="vis">
                  <xsl:call-template name="mk_vis_list">
                    <xsl:with-param name="els" select="Visible/Int"/>
                  </xsl:call-template>
                </xsl:variable>
                <xsl:call-template name="cons">
                  <xsl:with-param name="h" select="@formatnr"/>
                  <xsl:with-param name="t">
                    <xsl:call-template name="cons">
                      <xsl:with-param name="h" select="$shift"/>
                      <xsl:with-param name="t">
                        <xsl:call-template name="cons">
                          <xsl:with-param name="h" select="$plink"/>
                          <xsl:with-param name="t" select="$vis"/>
                        </xsl:call-template>
                      </xsl:with-param>
                    </xsl:call-template>
                  </xsl:with-param>
                </xsl:call-template>
              </xsl:for-each>
            </xsl:for-each>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- pretty printer - gets arguments, visibility info from pattern, -->
  <!-- format telling arities, the linked symbol and optionally right bracket -->
  <!-- parenth hints to put the whole expression in parentheses, but this -->
  <!-- is overrriden if the expression uses functor brackets -->
  <!-- #loci tells to print loci instead of arguments -->
  <xsl:template name="pp">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:param name="args"/>
    <xsl:param name="parenth"/>
    <xsl:param name="pid"/>
    <xsl:param name="loci"/>
    <xsl:variable name="pkey" select="concat(&apos;P_&apos;,$k)"/>
    <!-- pattern number given -->
    <xsl:choose>
      <xsl:when test="$pid&gt;0">
        <xsl:choose>
          <xsl:when test="key($pkey,$nr)[$pid=@relnr]">
            <xsl:for-each select="key($pkey,$nr)[$pid=@relnr]">
              <xsl:variable name="npid">
                <xsl:if test="@redefnr&gt;0">
                  <xsl:value-of select="$pid"/>
                </xsl:if>
              </xsl:variable>
              <xsl:call-template name="pp1">
                <xsl:with-param name="k" select="$k"/>
                <xsl:with-param name="nr" select="$nr"/>
                <xsl:with-param name="args" select="$args"/>
                <xsl:with-param name="vis" select="Visible/Int"/>
                <xsl:with-param name="fnr" select="@formatnr"/>
                <xsl:with-param name="parenth" select="$parenth"/>
                <xsl:with-param name="loci" select="$loci"/>
                <xsl:with-param name="pid" select="$npid"/>
              </xsl:call-template>
            </xsl:for-each>
          </xsl:when>
          <xsl:otherwise>
            <xsl:for-each select="document($patts,/)">
              <xsl:choose>
                <xsl:when test="key($pkey,$nr)[$pid=@relnr]">
                  <xsl:for-each select="key($pkey,$nr)[$pid=@relnr]">
                    <xsl:variable name="npid">
                      <xsl:if test="@redefnr&gt;0">
                        <xsl:value-of select="$pid"/>
                      </xsl:if>
                    </xsl:variable>
                    <xsl:call-template name="pp1">
                      <xsl:with-param name="k" select="$k"/>
                      <xsl:with-param name="nr" select="$nr"/>
                      <xsl:with-param name="args" select="$args"/>
                      <xsl:with-param name="vis" select="Visible/Int"/>
                      <xsl:with-param name="fnr" select="@formatnr"/>
                      <xsl:with-param name="parenth" select="$parenth"/>
                      <xsl:with-param name="loci" select="$loci"/>
                      <xsl:with-param name="pid" select="$npid"/>
                    </xsl:call-template>
                  </xsl:for-each>
                </xsl:when>
                <!-- failure, print in absolute notation -->
                <xsl:otherwise>
                  <xsl:call-template name="abs">
                    <xsl:with-param name="k" select="$k"/>
                    <xsl:with-param name="nr" select="$nr"/>
                  </xsl:call-template>
                  <xsl:text>(</xsl:text>
                  <xsl:call-template name="list">
                    <xsl:with-param name="separ">
                      <xsl:text>,</xsl:text>
                    </xsl:with-param>
                    <xsl:with-param name="elems" select="$args"/>
                  </xsl:call-template>
                  <xsl:text>)</xsl:text>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:for-each>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <!-- pattern number not given - take first suitable -->
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="key($pkey,$nr)">
            <xsl:for-each select="key($pkey,$nr)[position()=1]">
              <xsl:variable name="npid">
                <xsl:if test="@redefnr&gt;0">
                  <xsl:value-of select="@relnr"/>
                </xsl:if>
              </xsl:variable>
              <xsl:call-template name="pp1">
                <xsl:with-param name="k" select="$k"/>
                <xsl:with-param name="nr" select="$nr"/>
                <xsl:with-param name="args" select="$args"/>
                <xsl:with-param name="vis" select="Visible/Int"/>
                <xsl:with-param name="fnr" select="@formatnr"/>
                <xsl:with-param name="parenth" select="$parenth"/>
                <xsl:with-param name="loci" select="$loci"/>
                <xsl:with-param name="pid" select="$npid"/>
              </xsl:call-template>
            </xsl:for-each>
          </xsl:when>
          <xsl:otherwise>
            <xsl:for-each select="document($patts,/)">
              <xsl:choose>
                <xsl:when test="key($pkey,$nr)">
                  <xsl:for-each select="key($pkey,$nr)[position()=1]">
                    <xsl:variable name="npid">
                      <xsl:if test="@redefnr&gt;0">
                        <xsl:value-of select="@relnr"/>
                      </xsl:if>
                    </xsl:variable>
                    <xsl:call-template name="pp1">
                      <xsl:with-param name="k" select="$k"/>
                      <xsl:with-param name="nr" select="$nr"/>
                      <xsl:with-param name="args" select="$args"/>
                      <xsl:with-param name="vis" select="Visible/Int"/>
                      <xsl:with-param name="fnr" select="@formatnr"/>
                      <xsl:with-param name="parenth" select="$parenth"/>
                      <xsl:with-param name="loci" select="$loci"/>
                      <xsl:with-param name="pid" select="$npid"/>
                    </xsl:call-template>
                  </xsl:for-each>
                </xsl:when>
                <!-- failure, print in absolute notation -->
                <xsl:otherwise>
                  <xsl:call-template name="abs">
                    <xsl:with-param name="k" select="$k"/>
                    <xsl:with-param name="nr" select="$nr"/>
                  </xsl:call-template>
                  <xsl:text>(</xsl:text>
                  <xsl:call-template name="list">
                    <xsl:with-param name="separ">
                      <xsl:text>,</xsl:text>
                    </xsl:with-param>
                    <xsl:with-param name="elems" select="$args"/>
                  </xsl:call-template>
                  <xsl:text>)</xsl:text>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:for-each>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- it is legal to pass onlt #loci instead of #args here -->
  <!-- #pid is passed to abs, causes linking to patterns -->
  <xsl:template name="pp1">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:param name="args"/>
    <xsl:param name="vis"/>
    <xsl:param name="fnr"/>
    <xsl:param name="parenth"/>
    <xsl:param name="loci"/>
    <xsl:param name="pid"/>
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
        <xsl:when test="not($vis) or ($k=&apos;G&apos;)">
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
            <xsl:value-of select="concat(&quot;p&quot;,$paren_color)"/>
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
                    <xsl:with-param name="fnr" select="$fnr"/>
                  </xsl:call-template>
                </xsl:with-param>
                <xsl:with-param name="pid" select="$pid"/>
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
                <xsl:choose>
                  <xsl:when test="$loci&gt;0">
                    <xsl:choose>
                      <xsl:when test="$loci=&quot;2&quot;">
                        <xsl:call-template name="pconst">
                          <xsl:with-param name="nr" select="$x"/>
                        </xsl:call-template>
                      </xsl:when>
                      <xsl:otherwise>
                        <xsl:call-template name="ploci">
                          <xsl:with-param name="nr" select="$x"/>
                        </xsl:call-template>
                      </xsl:otherwise>
                    </xsl:choose>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:apply-templates select="$args[position() = $x]">
                      <xsl:with-param name="p" select="$np"/>
                    </xsl:apply-templates>
                  </xsl:otherwise>
                </xsl:choose>
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
                    <xsl:with-param name="fnr" select="$fnr"/>
                  </xsl:call-template>
                </xsl:with-param>
                <xsl:with-param name="pid" select="$pid"/>
              </xsl:call-template>
              <xsl:text> </xsl:text>
            </xsl:if>
            <xsl:for-each select="$vis">
              <xsl:if test="(position() = 1) and (($k=&apos;M&apos;) or ($k=&apos;L&apos;))">
                <xsl:text>of </xsl:text>
              </xsl:if>
              <xsl:if test="position() &gt; $la">
                <xsl:variable name="x" select="@x"/>
                <xsl:choose>
                  <xsl:when test="$loci&gt;0">
                    <xsl:choose>
                      <xsl:when test="$loci=&quot;2&quot;">
                        <xsl:call-template name="pconst">
                          <xsl:with-param name="nr" select="$x"/>
                        </xsl:call-template>
                      </xsl:when>
                      <xsl:otherwise>
                        <xsl:call-template name="ploci">
                          <xsl:with-param name="nr" select="$x"/>
                        </xsl:call-template>
                      </xsl:otherwise>
                    </xsl:choose>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:apply-templates select="$args[position()  = $x]">
                      <xsl:with-param name="p" select="$np"/>
                    </xsl:apply-templates>
                  </xsl:otherwise>
                </xsl:choose>
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
                <xsl:with-param name="pid" select="$pid"/>
              </xsl:call-template>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:for-each select="$vis">
          <xsl:if test="position() &lt;= $la">
            <xsl:variable name="x" select="@x"/>
            <xsl:choose>
              <xsl:when test="$loci&gt;0">
                <xsl:choose>
                  <xsl:when test="$loci=&quot;2&quot;">
                    <xsl:call-template name="pconst">
                      <xsl:with-param name="nr" select="$x"/>
                    </xsl:call-template>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:call-template name="ploci">
                      <xsl:with-param name="nr" select="$x"/>
                    </xsl:call-template>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:when>
              <xsl:otherwise>
                <xsl:apply-templates select="$args[position() = $x]">
                  <xsl:with-param name="p" select="$np"/>
                </xsl:apply-templates>
              </xsl:otherwise>
            </xsl:choose>
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
                <xsl:with-param name="fnr" select="$fnr"/>
              </xsl:call-template>
            </xsl:with-param>
            <xsl:with-param name="pid" select="$pid"/>
          </xsl:call-template>
          <xsl:if test="$k=&apos;G&apos;">
            <xsl:text>(#</xsl:text>
          </xsl:if>
          <xsl:text> </xsl:text>
        </xsl:if>
        <xsl:for-each select="$vis">
          <xsl:if test="(position() = 1) and (($k=&apos;M&apos;) or ($k=&apos;L&apos;))">
            <xsl:text>of </xsl:text>
          </xsl:if>
          <xsl:if test="position() &gt; $la">
            <xsl:variable name="x" select="@x"/>
            <xsl:choose>
              <xsl:when test="$loci&gt;0">
                <xsl:choose>
                  <xsl:when test="$loci=&quot;2&quot;">
                    <xsl:call-template name="pconst">
                      <xsl:with-param name="nr" select="$x"/>
                    </xsl:call-template>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:call-template name="ploci">
                      <xsl:with-param name="nr" select="$x"/>
                    </xsl:call-template>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:when>
              <xsl:otherwise>
                <xsl:apply-templates select="$args[position()  = $x]">
                  <xsl:with-param name="p" select="$np"/>
                </xsl:apply-templates>
              </xsl:otherwise>
            </xsl:choose>
            <xsl:if test="position() &lt; last()">
              <xsl:text>,</xsl:text>
            </xsl:if>
          </xsl:if>
        </xsl:for-each>
        <xsl:if test="$k=&apos;G&apos;">
          <xsl:text> #)</xsl:text>
        </xsl:if>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- apply[.]; if [not(position()=last())] { $sep1; `$j+position()`; $sep2; } }} -->
  <!-- pretty print variables and labels -->
  <xsl:template name="pvar">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$colored=&quot;1&quot;">
        <xsl:element name="font">
          <xsl:attribute name="color">
            <xsl:value-of select="$varcolor"/>
          </xsl:attribute>
          <xsl:text>b</xsl:text>
          <xsl:element name="sub">
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>b</xsl:text>
        <xsl:element name="sub">
          <xsl:value-of select="$nr"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="pconst">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$colored=&quot;1&quot;">
        <xsl:element name="font">
          <xsl:attribute name="color">
            <xsl:value-of select="$constcolor"/>
          </xsl:attribute>
          <xsl:text>c</xsl:text>
          <xsl:element name="sub">
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>c</xsl:text>
        <xsl:element name="sub">
          <xsl:value-of select="$nr"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="ploci">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$colored=&quot;1&quot;">
        <xsl:element name="font">
          <xsl:attribute name="color">
            <xsl:value-of select="$locicolor"/>
          </xsl:attribute>
          <xsl:text>a</xsl:text>
          <xsl:element name="sub">
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>a</xsl:text>
        <xsl:element name="sub">
          <xsl:value-of select="$nr"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="pschpvar">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$colored=&quot;1&quot;">
        <xsl:element name="font">
          <xsl:attribute name="color">
            <xsl:value-of select="$schpcolor"/>
          </xsl:attribute>
          <xsl:text>P</xsl:text>
          <xsl:element name="sub">
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>P</xsl:text>
        <xsl:element name="sub">
          <xsl:value-of select="$nr"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="pschfvar">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$colored=&quot;1&quot;">
        <xsl:element name="font">
          <xsl:attribute name="color">
            <xsl:value-of select="$schfcolor"/>
          </xsl:attribute>
          <xsl:text>F</xsl:text>
          <xsl:element name="sub">
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>F</xsl:text>
        <xsl:element name="sub">
          <xsl:value-of select="$nr"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="pppred">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$colored=&quot;1&quot;">
        <xsl:element name="font">
          <xsl:attribute name="color">
            <xsl:value-of select="$ppcolor"/>
          </xsl:attribute>
          <xsl:text>S</xsl:text>
          <xsl:element name="sub">
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>S</xsl:text>
        <xsl:element name="sub">
          <xsl:value-of select="$nr"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="ppfunc">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$colored=&quot;1&quot;">
        <xsl:element name="font">
          <xsl:attribute name="color">
            <xsl:value-of select="$pfcolor"/>
          </xsl:attribute>
          <xsl:text>H</xsl:text>
          <xsl:element name="sub">
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>H</xsl:text>
        <xsl:element name="sub">
          <xsl:value-of select="$nr"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="plab">
    <xsl:param name="nr"/>
    <xsl:element name="i">
      <xsl:choose>
        <xsl:when test="$colored=&quot;1&quot;">
          <xsl:element name="font">
            <xsl:attribute name="color">
              <xsl:value-of select="$labcolor"/>
            </xsl:attribute>
            <xsl:text>E</xsl:text>
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>E</xsl:text>
          <xsl:value-of select="$nr"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:element>
  </xsl:template>

  <xsl:template name="pcomment0">
    <xsl:param name="str"/>
    <xsl:element name="i">
      <xsl:choose>
        <xsl:when test="$colored=&quot;1&quot;">
          <xsl:element name="font">
            <xsl:attribute name="color">
              <xsl:value-of select="$commentcolor"/>
            </xsl:attribute>
            <xsl:text>:: </xsl:text>
            <xsl:value-of select="$str"/>
          </xsl:element>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>:: </xsl:text>
          <xsl:value-of select="$str"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:element>
  </xsl:template>

  <xsl:template name="pcomment">
    <xsl:param name="str"/>
    <xsl:call-template name="pcomment0">
      <xsl:with-param name="str" select="$str"/>
    </xsl:call-template>
    <xsl:element name="br"/>
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
    <xsl:variable name="alc">
      <xsl:call-template name="lc">
        <xsl:with-param name="s" select="$aid"/>
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
        </xsl:when>
        <xsl:otherwise>
          <xsl:attribute name="href">
            <xsl:value-of select="concat($alc, &quot;.&quot;, $ext, &quot;#&quot;,$k,$nr)"/>
          </xsl:attribute>
          <xsl:if test="$c">
            <xsl:attribute name="target">
              <xsl:text>_self</xsl:text>
            </xsl:attribute>
          </xsl:if>
        </xsl:otherwise>
      </xsl:choose>
      <xsl:if test="$titles=&quot;1&quot;">
        <xsl:attribute name="title">
          <xsl:value-of select="concat($aid,&quot;:&quot;,$mk,&quot;.&quot;,$nr)"/>
        </xsl:attribute>
      </xsl:if>
      <xsl:value-of select="$aid"/>
      <xsl:text>:</xsl:text>
      <xsl:if test="not($k=&quot;T&quot;)">
        <xsl:value-of select="$mk"/>
        <xsl:text> </xsl:text>
      </xsl:if>
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
          <xsl:for-each select="key($k,concat($anr,&apos;:&apos;,$nr))[position()=1]">
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

  <!-- translate constructor (notation) kinds to their mizar/mmlquery names -->
  <xsl:template name="mkind">
    <xsl:param name="kind"/>
    <xsl:param name="notat"/>
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
    <xsl:call-template name="pcomment">
      <xsl:with-param name="str" select="concat($aname, &quot;  semantic presentation&quot;)"/>
    </xsl:call-template>
    <xsl:element name="br"/>
    <xsl:for-each select="*">
      <xsl:apply-templates select="."/>
      <xsl:if test="(not(name()=&apos;Definiens&apos;)) and (not(name()=&apos;Reservation&apos;))">
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
    <xsl:choose>
      <xsl:when test="Verum">
        <xsl:element name="b">
          <xsl:text>canceled; </xsl:text>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates/>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:element name="br"/>
    <xsl:element name="br"/>
  </xsl:template>

  <!-- now used only when #mml=1 - in article the block has them -->
  <xsl:template match="ArgTypes">
    <xsl:if test="*">
      <xsl:element name="b">
        <xsl:text>let </xsl:text>
      </xsl:element>
      <xsl:call-template name="ploci">
        <xsl:with-param name="nr">
          <xsl:text>1</xsl:text>
        </xsl:with-param>
      </xsl:call-template>
      <xsl:text> be </xsl:text>
      <xsl:call-template name="alist">
        <xsl:with-param name="j">
          <xsl:text>1</xsl:text>
        </xsl:with-param>
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
    </xsl:if>
  </xsl:template>

  <!-- #indef tells not to use Argtypes (we are inside Definition) -->
  <xsl:template match="Constructor">
    <xsl:param name="indef"/>
    <xsl:param name="nl"/>
    <xsl:variable name="loci">
      <xsl:choose>
        <xsl:when test="$mml=&quot;1&quot;">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>2</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:if test="not($indef=&quot;1&quot;)">
      <xsl:apply-templates select="ArgTypes"/>
    </xsl:if>
    <xsl:if test="@redefnr&gt;0">
      <xsl:element name="b">
        <xsl:text>redefine </xsl:text>
      </xsl:element>
    </xsl:if>
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
    <xsl:if test="@redefnr&gt;0">
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
    <xsl:choose>
      <xsl:when test="@kind=&quot;G&quot;">
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
        <xsl:text>(# </xsl:text>
        <xsl:for-each select="Fields/Field">
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
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="@kind=&apos;V&apos;">
            <xsl:call-template name="ploci">
              <xsl:with-param name="nr" select="count(ArgTypes/Typ)"/>
            </xsl:call-template>
            <xsl:text> is </xsl:text>
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
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="pp">
              <xsl:with-param name="k" select="@kind"/>
              <xsl:with-param name="nr" select="@relnr"/>
              <xsl:with-param name="args" select="ArgTypes/Typ"/>
              <xsl:with-param name="loci" select="$loci"/>
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
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
    <xsl:choose>
      <xsl:when test="not($indef=&quot;1&quot;)">
        <xsl:text>;</xsl:text>
        <xsl:element name="br"/>
        <xsl:element name="br"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:if test="$nl=&quot;1&quot;">
          <xsl:text>;</xsl:text>
          <xsl:element name="br"/>
        </xsl:if>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- display synonym and antonym definiiotns -->
  <xsl:template match="NotationBlock/Pattern">
    <!-- pp1(#k=`@constrkind`,#nr=`@constrnr`,#vis=`Visible/Int`, -->
    <!-- #fnr=`@formatnr`, #loci="1"); <br; -->
    <xsl:variable name="loci">
      <xsl:choose>
        <xsl:when test="$mml=&quot;1&quot;">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>2</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:element name="a">
      <xsl:attribute name="NAME">
        <xsl:value-of select="concat(&quot;N&quot;,@kind,@nr)"/>
      </xsl:attribute>
      <xsl:element name="b">
        <xsl:choose>
          <xsl:when test="@antonymic">
            <xsl:text>antonym </xsl:text>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text>synonym </xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:element>
      <xsl:call-template name="pp1">
        <xsl:with-param name="k" select="@constrkind"/>
        <xsl:with-param name="nr" select="@constrnr"/>
        <xsl:with-param name="vis" select="Visible/Int"/>
        <xsl:with-param name="fnr" select="@formatnr"/>
        <xsl:with-param name="loci" select="$loci"/>
      </xsl:call-template>
    </xsl:element>
    <xsl:element name="b">
      <xsl:text> for </xsl:text>
    </xsl:element>
    <xsl:call-template name="pp">
      <xsl:with-param name="k" select="@constrkind"/>
      <xsl:with-param name="nr" select="@constrnr"/>
      <xsl:with-param name="pid" select="@redefnr"/>
      <xsl:with-param name="loci" select="$loci"/>
    </xsl:call-template>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <!-- ignore normal Patterns now -->
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
a.ref { font-size:x-small; }
a.ref:link { color:green; } 
a.ref:hover { color: red; } 
a.txt:link { color:black; } 
a.txt:hover { color: red; } 
span.hide { display: none; }
span.p1:hover { color : inherit; background-color : #BAFFFF; } 
span.p2:hover { color : inherit; background-color : #FFCACA; }
span.p3:hover { color : inherit; background-color : #FFFFBA; }
span.p4:hover { color : inherit; background-color : #CACAFF; }
span.p5:hover { color : inherit; background-color : #CAFFCA; }
span.p0:hover { color : inherit; background-color : #FFBAFF; }
.default { background-color: white; color: black; } 
.default:hover { background-color: white; color: black; }
</xsl:text>
      </xsl:element>
      <xsl:element name="head">
        <xsl:element name="script">
          <xsl:attribute name="type">
            <xsl:text>text/javascript</xsl:text>
          </xsl:attribute>
          <xsl:text>
&lt;!-- 
function hs(obj)
{
// document.getElementById(&apos;myimage&apos;).nextSibling.style.display = &apos;block&apos;;
if (obj.nextSibling.style.display == &apos;inline&apos;)
 { obj.nextSibling.style.display = &apos;none&apos;; }
else { if (obj.nextSibling.style.display == &apos;none&apos;)
 { obj.nextSibling.style.display = &apos;inline&apos;; }
 else { obj.nextSibling.style.display = &apos;inline&apos;;  }}
return false;
}

function hs2(obj)
{
if (obj.nextSibling.style.display == &apos;block&apos;)
 { obj.nextSibling.style.display = &apos;none&apos;; }
else { if (obj.nextSibling.style.display == &apos;none&apos;)
 { obj.nextSibling.style.display = &apos;block&apos;; }
 else { obj.nextSibling.style.display = &apos;none&apos;;  }}
return false;
}
// End --&gt;
</xsl:text>
        </xsl:element>
        <xsl:element name="base">
          <xsl:choose>
            <xsl:when test="$linking = &quot;s&quot;">
              <xsl:attribute name="target">
                <xsl:text>_self</xsl:text>
              </xsl:attribute>
            </xsl:when>
            <xsl:otherwise>
              <xsl:attribute name="target">
                <xsl:text>mmlquery</xsl:text>
              </xsl:attribute>
            </xsl:otherwise>
          </xsl:choose>
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
