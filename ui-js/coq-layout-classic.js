// The CoqLayoutClassic class.
// Copyright (C) 2015-2017 Mines ParisTech/ARMINES
//
// This class provides a plugabble side panel with proof and query
// buffers.

"use strict";

/***********************************************************************/
/* The CoqLayout class contains the goal, query, and packages buffer   */
/***********************************************************************/
class CoqLayoutClassic {

    html(base_path) {
        var html = `
    <div id="toolbar">
      <div style="position:relative; left:-34px; top:2px">
      <div style="position:absolute">
      <svg id="hide-panel" title="Toggle panel (F8)" width="32" height="32">
        <path d="M16.001,0C7.165,0,0,7.164,0,16.001S7.162,32,16.001,32C24.838,32,32,24.835,32,15.999S24.838,0,16.001,0L16.001,0z"/>
        <g>
	  <path fill="#FFFFFF" d="M14,4.212c0-0.895,0.607-1.617,1.501-1.617C16.393,2.595,17,3.317,17,4.212v11.124
		                  c0,0.892-0.607,1.614-1.499,1.614c-0.894,0-1.501-0.722-1.501-1.614V4.212z"/>
	  <path fill="#FFFFFF" d="M16.001,27.817c-6.244,0-11.321-5.08-11.321-11.321c0-4.049,2.188-7.817,5.711-9.831
		                  c0.772-0.441,1.761-0.173,2.203,0.6c0.444,0.775,0.174,1.761-0.6,2.206c-2.519,1.441-4.083,4.133-4.083,7.025
		                  c0,4.462,3.629,8.09,8.09,8.09c4.459,0,8.091-3.628,8.091-8.09c0-2.892-1.567-5.584-4.086-7.025
		                  c-0.773-0.444-1.043-1.431-0.599-2.206c0.444-0.773,1.43-1.044,2.203-0.6c3.523,2.014,5.711,5.782,5.711,9.831
		                  C27.32,22.737,22.243,27.817,16.001,27.817L16.001,27.817z"/>
        </g>
      </svg>
      </div>
      </div>
      <div class="exits">
        <a href="http://feever.fr/" target="_blank">
          <img src="${base_path}/ui-images/feever-logo.png" alt="FEEVER Logo" height="34" width="67"
               style="vertical-align: middle"/>
        </a>
        <a href="https://github.com/ejgallego/jscoq">Readme @ GitHub</a>
      </div> <!-- /#exits -->
      <span id="buttons">
        <img src="${base_path}/ui-images/up.png" width="21" height="24"
             alt="Up (Meta-P)" title="Up (Meta-P)" name="up"/>
        <img src="${base_path}/ui-images/down.png" width="21" height="25"
             alt="Down (Meta-N)" title="Down (Meta-N)" name="down"/>
        <img src="${base_path}/ui-images/to-cursor.png" width="38" height="24"
             alt="To cursor (Meta-Enter)" title="To cursor (Meta-Enter)" name="to-cursor"/>
      </span>
    </div> <!-- /#toolbar -->
    <div class="flex-container">
      <div id="goal-panel" class="flex-panel">
        <div class="caption">Goals</div>
        <div class="content" id="goal-text" data-lang="coq">
        </div>
      </div>
      <div class="msg-area flex-panel">
        <div class="caption">
          Messages
          <select name="msg_filter">
            <option value="0">Error</option>
            <option value="1">Warning</option>
            <option value="2">Notice</option>
            <option value="3" selected="selected">Info</option>
            <option value="4">Debug</option>
          </select>
        </div>
        <div class="content" id="query-panel"></div>
      </div>
      <div class="flex-panel collapsed">
        <div class="caption">Packages</div>
        <div id="packages-panel" class="content"></div>
      </div>
    </div>`;

        return html;
    }

    // We first initialize the providers.
    constructor(options) {

        // Our reference to the IDE, goal display & query buffer.
        this.ide   = document.getElementById(options.wrapper_id);

        this.panel = document.createElement('div');
        this.panel.id = 'panel-wrapper';
        this.panel.innerHTML = this.html(options.base_path);

        this.ide.appendChild(this.panel);

        // UI setup.
        this.proof    = document.getElementById('goal-text');
        this.query    = document.getElementById('query-panel');
        this.packages = document.getElementById('packages-panel');
        this.buttons  = document.getElementById('buttons');

        // XXXXXXX: This has to be fixed.
        this.log_css_rules = document.styleSheets[1].cssRules;

        var flex_container = this.panel.getElementsByClassName('flex-container')[0];
        flex_container.addEventListener('click', evt => { this.panelClickHandler(evt); });

        d3.select('select[name=msg_filter]')
            .on('change', () => this.filterLog(d3.event.target));
    }

    show() {
        this.ide.classList.remove('toggled');
    }

    hide() {
        this.ide.classList.add('toggled');
    }

    toggled() {
        return this.ide.classList.contains('toggled');
    }

    toggle() {

        if (this.toggled()) {
            this.show();
        }
        else {
            this.hide();
        }
    }


    // This is still not optimal.
    update_goals(str) {
        // TODO: Add diff/history of goals.
        // XXX: should send a message.
        this.proof.innerHTML = str;
    }

    // Add a log event received from Coq.
    log(text, level) {

        // Levels are taken from Coq itself:
        //   | Debug | Info | Notice | Warning | Error
        var item =
            d3.select(this.query)
                .append('div')
                .attr('class', level)
                .html(text);

        if (this.scrollTimeout) clearTimeout(this.scrollTimeout);

        this.scrollTimeout = setTimeout( () => {
            item.node().scrollIntoView(false);
            this.scrollTimeout = null;
        }, 1 );
    }

    filterLog(level_select) {

        // debugger;
        var length = level_select.getElementsByTagName('option').length;
        var min_log_level = parseInt(level_select.value, 10);
        var i;

        // XXXX!
        console.log('setting lvl', min_log_level);
        for(i = 0 ; i <= min_log_level ; i++)
            this.log_css_rules[i].style.display = 'block';

        for(i = min_log_level+1 ; i < length ; i++)
            this.log_css_rules[i].style.display = 'none';
    }

    // Execute a query to Coq
    query(query) {
        return true;
    }

    panelClickHandler(evt) {

        var target = evt.target;

        if(target.classList.contains('caption') &&

            target.parentNode.classList.contains('flex-panel')) {

            var panel = target.parentNode;

            if(panel.classList.contains('collapsed')) {

                panel.classList.remove('collapsed');

            } else {

                var panels_cpt = this.panel.getElementsByClassName('flex-panel').length;
                var collapsed_panels_cpt = this.panel.getElementsByClassName('collapsed').length;

                if(collapsed_panels_cpt + 1 >= panels_cpt) // at least one panel opened
                    return;

                panel.classList.add('collapsed');
            }
        }
    }
}

// Local Variables:
// js-indent-level: 4
// End:
