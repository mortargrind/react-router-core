import { createContext, useRef, useReducer, useLayoutEffect, createElement, useContext, useEffect, useMemo, useCallback, Children, isValidElement, Fragment } from 'react';
import PropTypes from 'prop-types';
import { createMemoryHistory, Action, parsePath } from 'history';

const readOnly =  obj => Object.freeze(obj) ;

function invariant(cond, message) {
  if (!cond) throw new Error(message);
}

function warning(cond, message) {
  if (!cond) {
    // eslint-disable-next-line no-console
    if (typeof console !== 'undefined') console.warn(message);

    try {
      // Welcome to debugging React Router!
      //
      // This error is thrown as a convenience so you can more easily
      // find the source for a warning that appears in the console by
      // enabling "pause on exceptions" in your JavaScript debugger.
      throw new Error(message); // eslint-disable-next-line no-empty
    } catch (e) {}
  }
}

const alreadyWarned = {};

function warningOnce(key, cond, message) {
  if (!cond && !alreadyWarned[key]) {
    alreadyWarned[key] = true;
     warning(false, message) ;
  }
}

const LocationContext = createContext({
  static: false
});

{
  LocationContext.displayName = 'Location';
}

const RouteContext = createContext({
  outlet: null,
  params: readOnly({}),
  pathname: '',
  basename: '',
  route: null
});

{
  RouteContext.displayName = 'Route';
} ///////////////////////////////////////////////////////////////////////////////
// COMPONENTS
///////////////////////////////////////////////////////////////////////////////

/**
 * A <Router> that stores all entries in memory.
 *
 * @see https://reactrouter.com/api/MemoryRouter
 */


function MemoryRouter({
  children,
  initialEntries,
  initialIndex
}) {
  let historyRef = useRef();

  if (historyRef.current == null) {
    historyRef.current = createMemoryHistory({
      initialEntries,
      initialIndex
    });
  }

  let history = historyRef.current;
  let [state, dispatch] = useReducer((_, action) => action, {
    action: history.action,
    location: history.location
  });
  useLayoutEffect(() => history.listen(dispatch), [history]);
  return createElement(Router, {
    children: children,
    action: state.action,
    location: state.location,
    navigator: history
  });
}

{
  MemoryRouter.displayName = 'MemoryRouter';
  MemoryRouter.propTypes = {
    children: PropTypes.node,
    initialEntries: PropTypes.arrayOf(PropTypes.oneOfType([PropTypes.string, PropTypes.shape({
      pathname: PropTypes.string,
      search: PropTypes.string,
      hash: PropTypes.string,
      state: PropTypes.object,
      key: PropTypes.string
    })])),
    initialIndex: PropTypes.number
  };
}
/**
 * Changes the current location.
 *
 * Note: This API is mostly useful in React.Component subclasses that are not
 * able to use hooks. In functional components, we recommend you use the
 * `useNavigate` hook instead.
 *
 * @see https://reactrouter.com/api/Navigate
 */


function Navigate({
  to,
  replace,
  state
}) {
  !useInRouterContext() ?  invariant(false, // TODO: This error is probably because they somehow have 2 versions of
  // the router loaded. We can help them understand how to avoid that.
  `<Navigate> may be used only in the context of a <Router> component.`)  : void 0;
   warning(!useContext(LocationContext).static, `<Navigate> must not be used on the initial render in a <StaticRouter>. ` + `This is a no-op, but you should modify your code so the <Navigate> is ` + `only ever rendered in response to some user interaction or state change.`) ;
  let navigate = useNavigate();
  useEffect(() => {
    navigate(to, {
      replace,
      state
    });
  });
  return null;
}

{
  Navigate.displayName = 'Navigate';
  Navigate.propTypes = {
    to: PropTypes.oneOfType([PropTypes.string, PropTypes.shape({
      pathname: PropTypes.string,
      search: PropTypes.string,
      hash: PropTypes.string
    })]).isRequired,
    replace: PropTypes.bool,
    state: PropTypes.object
  };
}
/**
 * Renders the child route's element, if there is one.
 *
 * @see https://reactrouter.com/api/Outlet
 */


function Outlet() {
  return useOutlet();
}

{
  Outlet.displayName = 'Outlet';
  Outlet.propTypes = {};
}
/**
 * Declares an element that should be rendered at a certain URL path.
 *
 * @see https://reactrouter.com/api/Route
 */


function Route({
  element = createElement(Outlet, null)
}) {
  return element;
}

{
  Route.displayName = 'Route';
  Route.propTypes = {
    caseSensitive: PropTypes.bool,
    children: PropTypes.node,
    element: PropTypes.element,
    path: PropTypes.string
  };
}
/**
 * Provides location context for the rest of the app.
 *
 * Note: You usually won't render a <Router> directly. Instead, you'll render a
 * router that is more specific to your environment such as a <BrowserRouter>
 * in web browsers or a <StaticRouter> for server rendering.
 *
 * @see https://reactrouter.com/api/Router
 */


function Router({
  children = null,
  action = Action.Pop,
  location,
  navigator,
  static: staticProp = false
}) {
  !!useInRouterContext() ?  invariant(false, `You cannot render a <Router> inside another <Router>.` + ` You never need more than one.`)  : void 0;
  return createElement(LocationContext.Provider, {
    children: children,
    value: {
      action,
      location,
      navigator,
      static: staticProp
    }
  });
}

{
  Router.displayName = 'Router';
  Router.propTypes = {
    children: PropTypes.node,
    action: PropTypes.oneOf(['POP', 'PUSH', 'REPLACE']),
    location: PropTypes.object.isRequired,
    navigator: PropTypes.shape({
      createHref: PropTypes.func.isRequired,
      push: PropTypes.func.isRequired,
      replace: PropTypes.func.isRequired,
      go: PropTypes.func.isRequired,
      block: PropTypes.func.isRequired
    }).isRequired,
    static: PropTypes.bool
  };
}
/**
 * A container for a nested tree of <Route> elements that renders the branch
 * that best matches the current location.
 *
 * @see https://reactrouter.com/api/Routes
 */


function Routes({
  basename = '',
  children
}) {
  let routes = createRoutesFromChildren(children);
  return useRoutes_(routes, basename);
}

{
  Routes.displayName = 'Routes';
  Routes.propTypes = {
    basename: PropTypes.string,
    children: PropTypes.node
  };
} ///////////////////////////////////////////////////////////////////////////////
// HOOKS
///////////////////////////////////////////////////////////////////////////////

/**
 * Blocks all navigation attempts. This is useful for preventing the page from
 * changing until some condition is met, like saving form data.
 *
 * @see https://reactrouter.com/api/useBlocker
 */


function useBlocker(blocker, when = true) {
  !useInRouterContext() ?  invariant(false, // TODO: This error is probably because they somehow have 2 versions of the
  // router loaded. We can help them understand how to avoid that.
  `useBlocker() may be used only in the context of a <Router> component.`)  : void 0;
  let navigator = useContext(LocationContext).navigator;
  useEffect(() => {
    if (!when) return;
    let unblock = navigator.block(tx => {
      let autoUnblockingTx = { ...tx,

        retry() {
          // Automatically unblock the transition so it can play all the way
          // through before retrying it. TODO: Figure out how to re-enable
          // this block if the transition is cancelled for some reason.
          unblock();
          tx.retry();
        }

      };
      blocker(autoUnblockingTx);
    });
    return unblock;
  }, [navigator, blocker, when]);
}
/**
 * Returns the full href for the given "to" value. This is useful for building
 * custom links that are also accessible and preserve right-click behavior.
 *
 * @see https://reactrouter.com/api/useHref
 */

function useHref(to) {
  !useInRouterContext() ?  invariant(false, // TODO: This error is probably because they somehow have 2 versions of the
  // router loaded. We can help them understand how to avoid that.
  `useHref() may be used only in the context of a <Router> component.`)  : void 0;
  let navigator = useContext(LocationContext).navigator;
  let path = useResolvedPath(to);
  return navigator.createHref(path);
}
/**
 * Returns true if this component is a descendant of a <Router>.
 *
 * @see https://reactrouter.com/api/useInRouterContext
 */

function useInRouterContext() {
  return useContext(LocationContext).location != null;
}
/**
 * Returns the current location object, which represents the current URL in web
 * browsers.
 *
 * Note: If you're using this it may mean you're doing some of your own
 * "routing" in your app, and we'd like to know what your use case is. We may
 * be able to provide something higher-level to better suit your needs.
 *
 * @see https://reactrouter.com/api/useLocation
 */

function useLocation() {
  !useInRouterContext() ?  invariant(false, // TODO: This error is probably because they somehow have 2 versions of the
  // router loaded. We can help them understand how to avoid that.
  `useLocation() may be used only in the context of a <Router> component.`)  : void 0;
  return useContext(LocationContext).location;
}
/**
 * Returns true if the URL for the given "to" value matches the current URL.
 * This is useful for components that need to know "active" state, e.g.
 * <NavLink>.
 *
 * @see https://reactrouter.com/api/useMatch
 */

function useMatch(pattern) {
  !useInRouterContext() ?  invariant(false, // TODO: This error is probably because they somehow have 2 versions of the
  // router loaded. We can help them understand how to avoid that.
  `useMatch() may be used only in the context of a <Router> component.`)  : void 0;
  let location = useLocation();
  return matchPath(pattern, location.pathname);
}
/**
 * Returns an imperative method for changing the location. Used by <Link>s, but
 * may also be used by other elements to change the location.
 *
 * @see https://reactrouter.com/api/useNavigate
 */

function useNavigate() {
  !useInRouterContext() ?  invariant(false, // TODO: This error is probably because they somehow have 2 versions of the
  // router loaded. We can help them understand how to avoid that.
  `useNavigate() may be used only in the context of a <Router> component.`)  : void 0;
  let locationContext = useContext(LocationContext);
  let navigator = locationContext.navigator;
  let {
    pathname,
    basename
  } = useContext(RouteContext);
  let activeRef = useRef(false);
  useEffect(() => {
    activeRef.current = true;
  });
  let navigate = useCallback((to, options = {}) => {
    if (activeRef.current) {
      if (typeof to === 'number') {
        navigator.go(to);
      } else {
        let path = resolvePath(to, pathname, basename);
        (!!options.replace ? navigator.replace : navigator.push)(path, options.state);
      }
    } else {
       warning(false, `You should call navigate() in a useEffect, not when ` + `your component is first rendered.`) ;
    }
  }, [navigator, pathname]);
  return navigate;
}
/**
 * Returns the element for the child route at this level of the route
 * hierarchy. Used internally by <Outlet> to render child routes.
 *
 * @see https://reactrouter.com/api/useOutlet
 */

function useOutlet() {
  return useContext(RouteContext).outlet;
}
/**
 * Returns an object of key/value pairs of the dynamic params from the current
 * URL that were matched by the route path.
 *
 * @see https://reactrouter.com/api/useParams
 */

function useParams() {
  return useContext(RouteContext).params;
}
/**
 * Resolves the pathname of the given `to` value against the current location.
 *
 * @see https://reactrouter.com/api/useResolvedPath
 */

function useResolvedPath(to) {
  let {
    pathname,
    basename
  } = useContext(RouteContext);
  return useMemo(() => resolvePath(to, pathname, basename), [to, pathname, basename]);
}
/**
 * Returns the element of the route that matched the current location, prepared
 * with the correct context to render the remainder of the route tree. Route
 * elements in the tree must render an <Outlet> to render their child route's
 * element.
 *
 * @see https://reactrouter.com/api/useRoutes
 */

function useRoutes(partialRoutes, basename = '') {
  !useInRouterContext() ?  invariant(false, // TODO: This error is probably because they somehow have 2 versions of the
  // router loaded. We can help them understand how to avoid that.
  `useRoutes() may be used only in the context of a <Router> component.`)  : void 0;
  let routes = useMemo(() => createRoutesFromArray(partialRoutes), [partialRoutes]);
  return useRoutes_(routes, basename);
}

function useRoutes_(routes, basename = '') {
  let {
    route: parentRoute,
    pathname: parentPathname,
    params: parentParams
  } = useContext(RouteContext);

  {
    // You won't get a warning about 2 different <Routes> under a <Route>
    // without a trailing *, but this is a best-effort warning anyway since we
    // cannot even give the warning unless they land at the parent route.
    let parentPath = parentRoute && parentRoute.path;
    warningOnce(parentPathname, !parentRoute || parentRoute.path.endsWith('*'), `You rendered descendant <Routes> (or called \`useRoutes\`) at "${parentPathname}"` + ` (under <Route path="${parentPath}">) but the parent route path has no trailing "*".` + ` This means if you navigate deeper, the parent won't match anymore and therefore` + ` the child routes will never render.` + `\n\n` + `Please change the parent <Route path="${parentPath}"> to <Route path="${parentPath}/*">.`);
  }

  basename = basename ? joinPaths([parentPathname, basename]) : parentPathname;
  let location = useLocation();
  let matches = useMemo(() => matchRoutes(routes, location, basename), [location, routes, basename]);

  if (!matches) {
    // TODO: Warn about nothing matching, suggest using a catch-all route.
    return null;
  } // Otherwise render an element.


  let element = matches.reduceRight((outlet, {
    params,
    pathname,
    route
  }) => {
    return createElement(RouteContext.Provider, {
      children: route.element,
      value: {
        outlet,
        params: readOnly({ ...parentParams,
          ...params
        }),
        pathname: joinPaths([basename, pathname]),
        basename,
        route
      }
    });
  }, null);
  return element;
} ///////////////////////////////////////////////////////////////////////////////
// UTILS
///////////////////////////////////////////////////////////////////////////////

/**
 * Creates a route config from an array of JavaScript objects. Used internally
 * by `useRoutes` to normalize the route config.
 *
 * @see https://reactrouter.com/api/createRoutesFromArray
 */


function createRoutesFromArray(array) {
  return array.map(partialRoute => {
    let route = {
      path: partialRoute.path || '/',
      caseSensitive: partialRoute.caseSensitive === true,
      element: partialRoute.element || createElement(Outlet, null)
    };

    if (partialRoute.children) {
      route.children = createRoutesFromArray(partialRoute.children);
    }

    return route;
  });
}
/**
 * Creates a route config from a React "children" object, which is usually
 * either a `<Route>` element or an array of them. Used internally by
 * `<Routes>` to create a route config from its children.
 *
 * @see https://reactrouter.com/api/createRoutesFromChildren
 */

function createRoutesFromChildren(children) {
  let routes = [];
  Children.forEach(children, element => {
    if (!isValidElement(element)) {
      // Ignore non-elements. This allows people to more easily inline
      // conditionals in their route config.
      return;
    }

    if (element.type === Fragment) {
      // Transparently support React.Fragment and its children.
      routes.push.apply(routes, createRoutesFromChildren(element.props.children));
      return;
    }

    let route = {
      path: element.props.path || '/',
      caseSensitive: element.props.caseSensitive === true,
      // Default behavior is to just render the element that was given. This
      // permits people to use any element they prefer, not just <Route> (though
      // all our official examples and docs use <Route> for clarity).
      element
    };

    if (element.props.children) {
      let childRoutes = createRoutesFromChildren(element.props.children);

      if (childRoutes.length) {
        route.children = childRoutes;
      }
    }

    routes.push(route);
  });
  return routes;
}
/**
 * Returns a path with params interpolated.
 *
 * @see https://reactrouter.com/api/generatePath
 */

function generatePath(path, params = {}) {
  return path.replace(/:(\w+)/g, (_, key) => {
    !(params[key] != null) ?  invariant(false, `Missing ":${key}" param`)  : void 0;
    return params[key];
  }).replace(/\/*\*$/, _ => params['*'] == null ? '' : params['*'].replace(/^\/*/, '/'));
}
/**
 * Matches the given routes to a location and returns the match data.
 *
 * @see https://reactrouter.com/api/matchRoutes
 */

function matchRoutes(routes, location, basename = '') {
  if (typeof location === 'string') {
    location = parsePath(location);
  }

  let pathname = location.pathname || '/';

  if (basename) {
    let base = basename.replace(/^\/*/, '/').replace(/\/+$/, '');

    if (pathname.startsWith(base)) {
      pathname = pathname === base ? '/' : pathname.slice(base.length);
    } else {
      // Pathname does not start with the basename, no match.
      return null;
    }
  }

  let branches = flattenRoutes(routes);
  rankRouteBranches(branches);
  let matches = null;

  for (let i = 0; matches == null && i < branches.length; ++i) {
    // TODO: Match on search, state too?
    matches = matchRouteBranch(branches[i], pathname);
  }

  return matches;
}

function flattenRoutes(routes, branches = [], parentPath = '', parentRoutes = [], parentIndexes = []) {
  routes.forEach((route, index) => {
    let path = joinPaths([parentPath, route.path]);
    let routes = parentRoutes.concat(route);
    let indexes = parentIndexes.concat(index); // Add the children before adding this route to the array so we traverse the
    // route tree depth-first and child routes appear before their parents in
    // the "flattened" version.

    if (route.children) {
      flattenRoutes(route.children, branches, path, routes, indexes);
    }

    branches.push([path, routes, indexes]);
  });
  return branches;
}

function rankRouteBranches(branches) {
  let pathScores = branches.reduce((memo, [path]) => {
    memo[path] = computeScore(path);
    return memo;
  }, {}); // Sorting is stable in modern browsers, but we still support IE 11, so we
  // need this little helper.

  stableSort(branches, (a, b) => {
    let [aPath,, aIndexes] = a;
    let aScore = pathScores[aPath];
    let [bPath,, bIndexes] = b;
    let bScore = pathScores[bPath];
    return aScore !== bScore ? bScore - aScore // Higher score first
    : compareIndexes(aIndexes, bIndexes);
  });
}

const paramRe = /^:\w+$/;
const dynamicSegmentValue = 2;
const emptySegmentValue = 1;
const staticSegmentValue = 10;
const splatPenalty = -2;

const isSplat = s => s === '*';

function computeScore(path) {
  let segments = path.split('/');
  let initialScore = segments.length;

  if (segments.some(isSplat)) {
    initialScore += splatPenalty;
  }

  return segments.filter(s => !isSplat(s)).reduce((score, segment) => score + (paramRe.test(segment) ? dynamicSegmentValue : segment === '' ? emptySegmentValue : staticSegmentValue), initialScore);
}

function compareIndexes(a, b) {
  let siblings = a.length === b.length && a.slice(0, -1).every((n, i) => n === b[i]);
  return siblings ? // If two routes are siblings, we should try to match the earlier sibling
  // first. This allows people to have fine-grained control over the matching
  // behavior by simply putting routes with identical paths in the order they
  // want them tried.
  a[a.length - 1] - b[b.length - 1] : // Otherwise, it doesn't really make sense to rank non-siblings by index,
  // so they sort equally.
  0;
}

function stableSort(array, compareItems) {
  // This copy lets us get the original index of an item so we can preserve the
  // original ordering in the case that they sort equally.
  let copy = array.slice(0);
  array.sort((a, b) => compareItems(a, b) || copy.indexOf(a) - copy.indexOf(b));
}

function matchRouteBranch(branch, pathname) {
  let routes = branch[1];
  let matchedPathname = '/';
  let matchedParams = {};
  let matches = [];

  for (let i = 0; i < routes.length; ++i) {
    let route = routes[i];
    let remainingPathname = matchedPathname === '/' ? pathname : pathname.slice(matchedPathname.length) || '/';
    let routeMatch = matchPath({
      path: route.path,
      caseSensitive: route.caseSensitive,
      end: i === routes.length - 1
    }, remainingPathname);
    if (!routeMatch) return null;
    matchedPathname = joinPaths([matchedPathname, routeMatch.pathname]);
    matchedParams = { ...matchedParams,
      ...routeMatch.params
    };
    matches.push({
      route,
      pathname: matchedPathname,
      params: readOnly(matchedParams)
    });
  }

  return matches;
}
/**
 * Performs pattern matching on a URL pathname and returns information about
 * the match.
 *
 * @see https://reactrouter.com/api/matchPath
 */


function matchPath(pattern, pathname) {
  if (typeof pattern === 'string') {
    pattern = {
      path: pattern
    };
  }

  let {
    path,
    caseSensitive = false,
    end = true
  } = pattern;
  let [matcher, paramNames] = compilePath(path, caseSensitive, end);
  let match = pathname.match(matcher);
  if (!match) return null;
  let matchedPathname = match[1];
  let values = match.slice(2);
  let params = paramNames.reduce((memo, paramName, index) => {
    memo[paramName] = safelyDecodeURIComponent(values[index], paramName);
    return memo;
  }, {});
  return {
    path,
    pathname: matchedPathname,
    params
  };
}

function compilePath(path, caseSensitive, end) {
  let keys = [];
  let source = '^(' + path.replace(/^\/*/, '/') // Make sure it has a leading /
  .replace(/\/?\*?$/, '') // Ignore trailing / and /*, we'll handle it below
  .replace(/[\\.*+^$?{}|()[\]]/g, '\\$&') // Escape special regex chars
  .replace(/:(\w+)/g, (_, key) => {
    keys.push(key);
    return '([^\\/]+)';
  }) + ')';

  if (path.endsWith('*')) {
    if (path.endsWith('/*')) {
      source += '\\/?'; // Don't include the / in params['*']
    }

    keys.push('*');
    source += '(.*)';
  } else if (end) {
    source += '\\/?';
  }

  if (end) source += '$';
  let flags = caseSensitive ? undefined : 'i';
  let matcher = new RegExp(source, flags);
  return [matcher, keys];
}

function safelyDecodeURIComponent(value, paramName) {
  try {
    return decodeURIComponent(value.replace(/\+/g, ' '));
  } catch (error) {
     warning(false, `The value for the URL param "${paramName}" will not be decoded because` + ` the string "${value}" is a malformed URL segment. This is probably` + ` due to a bad percent encoding (${error}).`) ;
    return value;
  }
}
/**
 * Returns a resolved path object relative to the given pathname.
 *
 * @see https://reactrouter.com/api/resolvePath
 */


function resolvePath(to, fromPathname = '/', basename = '') {
  let {
    pathname: toPathname,
    search = '',
    hash = ''
  } = typeof to === 'string' ? parsePath(to) : to;
  let pathname = toPathname ? resolvePathname(toPathname, toPathname.startsWith('/') ? basename ? `/${basename}` : '/' : fromPathname) : fromPathname;
  return {
    pathname,
    search,
    hash
  };
}

const trimTrailingSlashes = path => path.replace(/\/+$/, '');

const normalizeSlashes = path => path.replace(/\/\/+/g, '/');

const joinPaths = paths => normalizeSlashes(paths.join('/'));

const splitPath = path => normalizeSlashes(path).split('/');

function resolvePathname(toPathname, fromPathname) {
  let segments = splitPath(trimTrailingSlashes(fromPathname));
  let relativeSegments = splitPath(toPathname);
  relativeSegments.forEach(segment => {
    if (segment === '..') {
      // Keep the root "" segment so the pathname starts at /
      if (segments.length > 1) segments.pop();
    } else if (segment !== '.') {
      segments.push(segment);
    }
  });
  return segments.length > 1 ? joinPaths(segments) : '/';
}

export { MemoryRouter, Navigate, Outlet, Route, Router, Routes, createRoutesFromArray, createRoutesFromChildren, generatePath, matchPath, matchRoutes, resolvePath, useBlocker, useHref, useInRouterContext, useLocation, useMatch, useNavigate, useOutlet, useParams, useResolvedPath, useRoutes };
//# sourceMappingURL=react-router.development.js.map
