// The CoqLayoutClassic class.
// Copyright (C) 2015-2017 Mines ParisTech/ARMINES
//
// This class provides a plugabble side panel with proof and query
// buffers.

import { SettingsPanel } from './settings.js';

"use strict";

/***********************************************************************/
/* The CoqLayout class contains the goal, query, and packages buffer   */
/***********************************************************************/

/**
 * Classical layout: a right panel containing a toolbar with buttons at the 
 * top, and a main area divided vertically into three collapsible panes.
 * Also shows a power button that hides or shows the panel.
 */
export class CoqLayoutClassic {

    html(params) {
        var {base_path, backend, kb} = params;
        return `
    <svg id="hide-panel" viewBox="0 0 32 32" title="Toggle panel (F8)">
      <path d="M16.001,0C7.165,0,0,7.164,0,16.001S7.162,32,16.001,32C24.838,32,32,24.835,32,15.999S24.838,0,16.001,0L16.001,0z"/>
      <g>
        <path fill="#FFFFFF" d="M14.5,4.212c0-0.895,0.607-1.617,1.501-1.617c0.893,0,1.5,0.722,1.5,1.617v11.124
                            c0,0.892-0.607,1.614-1.499,1.614c-0.894,0-1.501-0.722-1.501-1.614z"/>
        <path fill="#FFFFFF" d="M16,27.317c-6.244,0-11.321-5.08-11.321-11.321c0-4.049,2.188-7.817,5.711-9.831
                            c0.772-0.441,1.761-0.173,2.203,0.6c0.444,0.775,0.174,1.761-0.6,2.206c-2.519,1.441-4.083,4.133-4.083,7.025
                            c0,4.462,3.629,8.09,8.09,8.09c4.459,0,8.091-3.628,8.091-8.09c0-2.892-1.567-5.584-4.086-7.025
                            c-0.773-0.444-1.043-1.431-0.599-2.206c0.444-0.773,1.43-1.044,2.203-0.6c3.523,2.014,5.711,5.782,5.711,9.831
                            C27.32,22.237,22.243,27.317,16.001,27.317z"/>
      </g>
    </svg>        
    <div id="toolbar">
      <div class="exits">
        <a href="https://coq.now.sh">
          <img class="${backend}-logo" src="${base_path}/ui-images/${backend}-logo.svg" alt="js"><i>+</i><!--
            --><img class="coq-logo" src="${base_path}/ui-images/coq-logo.png" alt="Coq">
        </a>
      </div> <!-- /.exits -->
      <span id="buttons">
        <button name="up"          alt="Up (${kb.up})"              title="Up (${kb.up})"></button><!--
     --><button name="down"        alt="Down (${kb.down})"          title="Down (${kb.down})"></button>
        <button name="to-cursor"   alt="To cursor (${kb.cursor})"   title="To cursor (${kb.cursor})"></button>
        <button name="interrupt"   alt="Interrupt Worker (Esc)"     title="Interrupt Worker (Esc)"></button>
        <button name="reset"       alt="Reset worker"               title="Reset worker"></button>
      </span>
      <div class="exits right">
        <svg class="app-menu-button" viewBox="0 0 80 80">
            <circle cx="40" cy="24" r="5"></circle>
            <circle cx="40" cy="40" r="5"></circle>
            <circle cx="40" cy="56" r="5"></circle>
        </svg>    
      </div> <!-- /.exits -->
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
    }

    /**
     * Initializes the UI layout.
     * @param {object} options jsCoq options; used keys are:
     *   - wrapper_id: element id of the IDE container
     *   - base_path: URL for the root directory of jsCoq
     *   - theme: jsCoq theme to use for the panel ('light' or 'dark')
     * @param {object} params HTML template parameters; used keys are:
     *   - kb: key-binding tooltips for actions {up, down, cursor}
     */
    constructor(options, params) {

        this.options = options;

        // Our reference to the IDE, goal display & query buffer.
        this.ide   = document.getElementById(options.wrapper_id);
        this.ide.classList.add('jscoq-ide', `layout-${options.layout || 'flex'}`);

        this.panel = document.createElement('div');
        this.panel.id = 'panel-wrapper';
        this.panel.innerHTML = this.html({base_path: options.base_path,
            backend: JsCoqGlobal.backend, ...params});

        this.ide.appendChild(this.panel);

        // UI setup.
        this.proof    = this.panel.querySelector('#goal-text');
        this.query    = this.panel.querySelector('#query-panel');
        this.packages = this.panel.querySelector('#packages-panel');
        this.buttons  = this.panel.querySelector('#buttons');
        this.menubtn  = this.panel.querySelector('.app-menu-button');
        this.settings = new SettingsPanel();

        var flex_container = this.panel.getElementsByClassName('flex-container')[0];
        flex_container.addEventListener('click', evt => { this.panelClickHandler(evt); });

        this.onToggle = evt => {};
        this.panel.querySelector('#hide-panel')
            .addEventListener('click', evt => this.toggle() );

        this._setButtons(false); // starts disabled

        this.onAction = evt => {};
        this.buttons.addEventListener('click', evt => this.onAction(evt));

        this.menubtn.addEventListener('mousedown', () =>
            this.settings.toggle());
        this.settings.active.observe(active =>
            this.menubtn.classList.toggle('active', active));

        // Configure log
        this.log_levels = ['Error', 'Warning', 'Notice', 'Info', 'Debug']
        $(this.panel).find('select[name=msg_filter]')
            .on('change', ev => this.filterLog(parseInt(ev.target.value)));
        this.filterLog(3); // Info

        this.configure(options);

        this._setupSettings();
        this._preloadImages();
    }

    /**
     * Configure or re-configure UI based on CoqManager options.
     * @param {object} options 
     */
    configure(options) {
        if (options.theme) {
            this.panel.classList.remove(...this.panel.classList);
            this.panel.classList.add(`jscoq-theme-${options.theme}`);
        }
        this.settings.configure({
            theme: options.theme,
            company: options.editor && options.editor.mode &&
                     options.editor.mode['company-coq']
        });
    }

    show() {
        this.ide.classList.add('goals-active');
        this.ide.classList.remove('toggled');
        this.onToggle({target: this, shown: true});
    }

    hide() {
        this.ide.classList.remove('goals-active');
        this.ide.classList.add('toggled');
        this.onToggle({target: this, shown: false});
    }

    isVisible() {
        return !this.ide.classList.contains('toggled');
    }

    toggle() {
        this.isVisible() ? this.hide() : this.show();
    }

    splash(version_info, msg, mode='wait') {
        var above = $(this.proof).find('.splash-above'), 
            image = $(this.proof).find('.splash-image'), 
            below = $(this.proof).find('.splash-below');

        var overlay = `${this.options.base_path}/ui-images/${mode}.gif`;

        if (!(above.length && image.length && below.length)) {
            $(this.proof).empty().append(
                above = $('<p>').addClass('splash-above'),
                $('<div>').addClass('splash-middle').append(
                    image = $('<div>').append($('<img>'))
                ),
                below = $('<p>').addClass('splash-below')
            )
        }

        if (version_info) above.text(version_info);
        if (msg)          below.text(msg);
        
        image[0].classList = [];
        image.addClass(['splash-image', mode]);
        var img = image.find('img');
        if (img.attr('src') !== overlay) img.attr('src', overlay);
    }

    createOutline() {
        var outline_pane = $('<div>').attr('id', 'outline-pane');
        $(this.ide).prepend(outline_pane);
        requestAnimationFrame(() => $(this.ide).addClass('outline-active'));
        return this.outline = outline_pane[0];
    }

    /**
     * Shows a notice in the main goal pane (reserved for important messages,
     * such as during startup).
     * @param {string} msg message text
     */
    systemNotification(msg) {
        $(this.proof).append($('<p>').addClass('system').text(msg));
    }

    _setButtons(enabled) {
        $(this.buttons).find('button').attr('disabled', !enabled);
        enabled ? this.buttons.classList.remove('disabled') 
                : this.buttons.classList.add('disabled');
    }

    toolbarOn() {
        // Enable the button actions and show them.
        this._setButtons(true);
        this.ide.classList.remove('on-hold');
    }

    toolbarOff() {
        // Disable the button actions and dim them.
        this._setButtons(false);
        this.ide.classList.add('on-hold');
    }

    // This is still not optimal.
    update_goals(content) {
        // TODO: Add diff/history of goals.
        // XXX: should send a message.
        $(this.proof).html(content);
    }

    // Add a log event received from Coq.
    log(text, level, attrs={}) {
        attrs = attrs || {};  // attrs can be `null` as well

        // Levels are taken from Coq itself:
        //   | Debug | Info | Notice | Warning | Error
        var item = $('<div>').addClass(level).html(text).attr(attrs),
            prev = $(this.query).children(':visible').last();

        if (attrs['data-coq-sid'] !== undefined)
            this.logSep(attrs['data-coq-sid'], item, prev);

        $(this.query).append(item);

        if (this.isLogVisible(level)) {
            if (this.scrollTimeout) clearTimeout(this.scrollTimeout);

            if (attrs.fast)
                this.query.scrollTo({top: this.query.scrollHeight});
            else
                this.scrollTimeout = setTimeout( () => {
                    this.query.scrollTo({top: this.query.scrollHeight,
                                         behavior: 'smooth'});
                }, 1 );
        }

        return item;
    }

    logSep(sid, item, prev) {
        if (sid === prev.attr('data-coq-sid')) {
            prev.removeClass('coq-sid-end');
            item.addClass('coq-sid-end');
        }
        else {
            item.addClass(['coq-sid-start', 'coq-sid-end'].concat(
                prev.hasClass('coq-sid-end') ? ['coq-prev-end'] : []));
        }
    }

    /**
     * Readjusts separators for the entire log when the level changes.
     * (called from filterLog)
     */
    logSepReadjust() {
        for (let item of $(this.query).find('.coq-sid-start')) {
            // XXX not very efficient :(
            if ($(item).prevUntil(':visible').prev('.coq-sid-end:visible').length)
                $(item).addClass('coq-prev-end');
            else
                $(item).removeClass('coq-prev-end');
        }
    }

    filterLog(level_select) {
        var i;

        if (typeof level_select == 'string')
            level_select = this.log_levels.indexOf(level_select);

        console.log('setting log level', level_select);
        for(i = 0 ; i <= level_select ; i++)
            this.query.classList.add(`show-${this.log_levels[i]}`);
        for(i = level_select+1 ; i < this.log_levels.length ; i++)
            this.query.classList.remove(`show-${this.log_levels[i]}`);

        this.log_level = level_select;

        requestAnimationFrame(() => {
            this.query.scrollTo({top: this.query.scrollHeight});  // only reasonable thing to do
            this.logSepReadjust();
        });
    }

    isLogVisible(level) {
        if (typeof level == 'string')
            level = this.log_levels.indexOf(level);

        return level <= this.log_level;
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

    /**
     * Set up hooks for when user changes settings.
     */
    _setupSettings() {
        this.settings.model.theme.observe(theme => {
            this.configure({theme});
        });
    }

    /**
     * Auxiliary function to improve UX by preloading images.
     */
    _preloadImages() {
        var imgs_dir = `${this.options.base_path}/ui-images`,
            img_fns = ['jscoq-splash.png', 'egg.png'];

        for (let fn of img_fns) {
            new Image().src = `${imgs_dir}/${fn}`;
        }
    }
}

// Local Variables:
// js-indent-level: 4
// End:
